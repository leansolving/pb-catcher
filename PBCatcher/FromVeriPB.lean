/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import Lean
import Std
import PBCatcher.PseudoBoolean

/-!
# VeriPB Proof Verification

Parser and metaprogram for VeriPB kernel-format proofs. This module parses
DIMACS CNF, OPB and VeriPB proof files, constructs proof terms using the
soundness lemmas from `PseudoBoolean.lean`, and produces Lean theorems.

## Parsed proof format

The parser accepts every statement that `veripb --elaborate` (VeriPB 3.0.1)
writes, see `ProofStep`. Parsing a statement does not mean that a checker
accepts it: the reflection checker (`Reflect.lean`) and the Expr-level
builder below support a subset and reject the rest.

## Variable names

A variable `x<N>` (decimal `N ≥ 1` without leading zeros) has index `N - 1`.
Every other name gets an index from a `VarTable`: the OPB parser assigns
named variables the indices above the largest `x<N>` index in order of first
appearance, and the proof parser assigns a fresh index (one above the
formula's variables and every `x<N>` of the proof; the count then grows) to
a name that first appears in a `red`/`dom` constraint or witness, a
checked-deletion witness, an order variable declaration, or a `sol`/`soli`
assignment (VeriPB adds unknown names there too). An unknown name anywhere
else is a parse error. The parser
rewrites every variable to the canonical string `x<idx+1>`, so the
downstream converters (`opbLitToPB`, `parseSubstPairs`) only see `x<N>`.

## Main definitions

* `PBCatcher.parseDimacs` — DIMACS CNF parser
* `PBCatcher.parseOPBNamed` / `PBCatcher.parseOPB` — OPB parser
* `PBCatcher.parseVeriPBProofWith` / `PBCatcher.parseVeriPBProof` — kernel proof parser
* `veripb_proof` — command that registers a kernel-verified theorem
* `from_veripb` — term elaborator for inline CNF/proof strings
* `veripb_proof_file` — command that loads CNF/proof from files
* `from_veripb_file` — term elaborator with file loading
-/

namespace PBCatcher

/-! ### Variable table -/

/-- Indices of the variables that are not written `x<N>`. `owned` is the set
of indices held by such names; `numVars` is one above the largest index in
use (by a name or by an `x<N>` seen so far). -/
structure VarTable where
  names : Std.HashMap String Nat := {}
  owned : Std.HashSet Nat := {}
  numVars : Nat := 0

/-- Build a table from `(name, index)` pairs and a variable count. -/
def VarTable.ofList (names : List (String × Nat)) (numVars : Nat) : VarTable :=
  names.foldl (init := { numVars := numVars }) fun t (n, i) =>
    { names := t.names.insert n i, owned := t.owned.insert i,
      numVars := max t.numVars (i + 1) }

/-- The named variables as `(name, index)` pairs sorted by index. -/
def VarTable.toList (t : VarTable) : List (String × Nat) :=
  t.names.toList.mergeSort fun a b => a.2 ≤ b.2

/-- Byte `i` of `s`'s UTF-8 encoding (`0` if out of range). -/
@[inline] private def byteAt (s : String) (i : Nat) : UInt8 :=
  if h : i < s.utf8ByteSize then
    s.getUTF8Byte ⟨i⟩ (by simpa [String.Pos.Raw.lt_iff] using h)
  else 0

/-- `s` without its first `k` bytes is `x<N>` with `N ≥ 1` written in
decimal without leading zeros: `some (N-1)`. -/
def canonXIndexAt? (s : String) (k : Nat) : Option Nat := Id.run do
  let n := s.utf8ByteSize
  -- 120 = 'x', 48..57 = '0'..'9'
  if k + 2 > n || byteAt s k != 120 then return none
  let b := byteAt s (k + 1)
  if b < 49 || b > 57 then return none
  let mut v := 0
  for i in [k + 1:n] do
    let b := byteAt s i
    if b < 48 || b > 57 then return none
    v := v * 10 + (b - 48).toNat
  return some (v - 1)

/-- `x<N>` with `N ≥ 1` written in decimal without leading zeros: `some (N-1)`. -/
@[inline] def canonXIndex? (name : String) : Option Nat := canonXIndexAt? name 0

/-- Canonical name of variable index `i`. -/
@[inline] def canonVarName (i : Nat) : String := s!"x{i + 1}"

/-- A proof-file variable name: at least two characters, starting with an
ASCII letter, `_` or `$` (VeriPB auxiliary variables). -/
def isVarName (s : String) : Bool :=
  -- the first character is ASCII, so two bytes mean two characters
  s.utf8ByteSize ≥ 2 &&
  (let c := s.front; c.isAlpha || c == '_' || c == '$')

/-- A nonempty string of decimal digits `[0-9]+`. -/
def isDecDigits (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

/-- An integer token `[+-]?[0-9]+` (VeriPB's lexers; Lean's `String.toNat?`
also accepts `_` separators, which VeriPB does not). -/
def isIntToken (s : String) : Bool :=
  isDecDigits s || ((s.startsWith "+" || s.startsWith "-") && isDecDigits (s.drop 1).toString)

/-- Parse an integer token `[+-]?[0-9]+`. -/
def intTokenVal? (s : String) : Option Int :=
  if !isIntToken s then none
  else if s.startsWith "+" then (s.drop 1).toString.toInt? else s.toInt?

/-- Parse a natural number token `[0-9]+`. -/
def natTokenVal? (s : String) : Option Nat :=
  if isDecDigits s then s.toNat? else none

-- Token-based parser infrastructure

/-- Parser state: token stream, position, variable table, and whether an
unknown variable name may be given a fresh index (`allowFresh`). -/
structure ParseState where
  tokens : Array String
  pos : Nat
  vars : VarTable := {}
  allowFresh : Bool := false
  /-- Every variable index must be below this bound (see
  `parseVeriPBProofWith`). -/
  varBound : Nat

/-- Parser monad: Except for errors, State for position. -/
abbrev ParseM := EStateM String ParseState

/-- Peek at the current token without consuming it. -/
def peek : ParseM String := do
  let s ← get
  if h : s.pos < s.tokens.size then
    return s.tokens[s.pos]
  else
    throw "unexpected end of input"

/-- Peek `k` tokens ahead (`peekAt 0 = peek`); `""` past the end. -/
def peekAt (k : Nat) : ParseM String := do
  let s ← get
  return s.tokens.getD (s.pos + k) ""

/-- Consume and return the current token. -/
def next : ParseM String := do
  let s ← get
  if h : s.pos < s.tokens.size then
    let tok := s.tokens[s.pos]
    set { s with pos := s.pos + 1 }
    return tok
  else
    throw "unexpected end of input"

/-- Expect a specific token. -/
def expect (tok : String) : ParseM Unit := do
  let t ← next
  if t != tok then
    throw s!"expected '{tok}', got '{t}'"

/-- Expect and consume a semicolon. -/
def expectSemicolon : ParseM Unit := expect ";"

/-- Consume the current token if it equals `tok`. -/
def accept (tok : String) : ParseM Bool := do
  if (← peekAt 0) == tok then
    let _ ← next
    return true
  else return false

/-- Try to parse a natural number from the current token. -/
def parseNat : ParseM Nat := do
  let tok ← next
  match natTokenVal? tok with
  | some n => return n
  | none => throw s!"expected natural number, got '{tok}'"

/-- Parse a signed integer token (`5`, `+5`, `-5`). -/
def parseInt : ParseM Int := do
  let tok ← next
  match intTokenVal? tok with
  | some n => return n
  | none => throw s!"expected integer, got '{tok}'"

/-- Resolve a variable name to its index (see the module doc), given
`cx = canonXIndex? name`. -/
def resolveVarIdx (name : String) (cx : Option Nat) : ParseM Nat := do
  let s ← get
  match cx with
  | some i =>
    if !s.vars.owned.isEmpty && s.vars.owned.contains i then
      throw s!"variable '{name}' collides with a named variable of the same index"
    if i ≥ s.varBound then
      throw s!"variable index of '{name}' too large"
    if i + 1 > s.vars.numVars then
      set { s with vars := { s.vars with numVars := i + 1 } }
    return i
  | none =>
    if !isVarName name then
      throw s!"invalid variable name '{name}'"
    match s.vars.names[name]? with
    | some i => return i
    | none =>
      if !s.allowFresh then
        throw s!"unknown variable '{name}'"
      let i := s.vars.numVars
      if i ≥ s.varBound then
        throw s!"too many variables (fresh name '{name}')"
      set { s with vars := { names := s.vars.names.insert name i,
                             owned := s.vars.owned.insert i,
                             numVars := i + 1 } }
      return i

/-- Resolve a variable name to its index (see the module doc). -/
@[inline] def resolveVar (name : String) : ParseM Nat :=
  resolveVarIdx name (canonXIndex? name)

/-- Run `x` with fresh variable names allowed. -/
def withFresh {α : Type} (x : ParseM α) : ParseM α := do
  let old := (← get).allowFresh
  modify fun s => { s with allowFresh := true }
  let r ← x
  modify fun s => { s with allowFresh := old }
  return r

/-! ### Tokenizer

Byte-level scanner over the UTF-8 encoding of the input. Tokens are maximal
runs of bytes other than space, tab, CR, LF and `;`; a `;` is always a token
of its own. Comments are skipped:
* `%` up to the end of the line, anywhere (VeriPB 3);
* with `dimacsComments` (DIMACS input only), a line whose first non-blank
  byte is `c` followed by a blank or the end of the line.
All separators are ASCII, so they never occur inside a multi-byte UTF-8
sequence; token boundaries are therefore character boundaries and every
extracted token is a valid UTF-8 string. -/

@[inline] private def isBlankByte (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == 13

@[inline] private def isSepByte (b : UInt8) : Bool :=
  isBlankByte b || b == 10 || b == 59 || b == 37

/-- Tokenize a string: split on blanks, separate semicolons, drop comments. -/
def tokenize (s : String) (dimacsComments : Bool := false) : Array String := Id.run do
  let n := s.utf8ByteSize
  let mut toks : Array String := Array.mkEmpty (n / 3)
  let mut i := 0
  while i < n do
    -- line start: skip blanks, detect comment lines
    let mut j := i
    while j < n && isBlankByte (byteAt s j) do j := j + 1
    let b := byteAt s j
    -- 37 = '%', 99 = 'c'
    let isComment := j < n && (b == 37 ||
      (dimacsComments && b == 99 &&
        (j + 1 ≥ n || isBlankByte (byteAt s (j + 1)) || byteAt s (j + 1) == 10)))
    let mut k := j
    if isComment then
      while k < n && byteAt s k != 10 do k := k + 1
    else
      while k < n do
        let c := byteAt s k
        if c == 10 then break
        else if c == 37 then
          -- `%` comment up to the end of the line
          while k < n && byteAt s k != 10 do k := k + 1
        else if isBlankByte c then k := k + 1
        else if c == 59 then
          toks := toks.push ";"
          k := k + 1
        else
          let start := k
          k := k + 1
          while k < n && !isSepByte (byteAt s k) do k := k + 1
          toks := toks.push (String.Pos.Raw.extract s ⟨start⟩ ⟨k⟩)
    i := k + 1
  return toks

-- Parsed CNF types

/-- A DIMACS clause: list of signed integers (positive = pos literal, negative = neg). -/
abbrev DimacsClause := List Int

/-- Parsed DIMACS CNF formula. -/
structure DimacsFormula where
  numVars : Nat
  numClauses : Nat
  clauses : Array DimacsClause
  deriving Repr

-- DIMACS CNF parser

/-- Parse a DIMACS literal (nonzero integer) into Sat.PB.Literal.
    DIMACS variable i (1-indexed) maps to PB variable (i-1) (0-indexed). -/
def dimacsLitToPB (lit : Int) : Except String Sat.PB.Literal :=
  if lit > 0 then
    .ok (.pos (lit.toNat - 1))
  else if lit < 0 then
    .ok (.neg ((-lit).toNat - 1))
  else
    .error "DIMACS literal 0 is not a valid literal"

/-- Convert a DIMACS clause to a PB constraint.
    Clause `[l1, l2, ..., lk]` becomes `1·l1 + 1·l2 + ... + 1·lk >= 1`. -/
def dimacsClauseToPB (clause : DimacsClause) : Except String Sat.PB.Constr := do
  let terms ← clause.mapM fun lit => do
    let pbLit ← dimacsLitToPB lit
    return (1, pbLit)
  return ⟨terms, 1⟩

/-- Parse DIMACS CNF format from a token stream.
    Expected: `p cnf <numVars> <numClauses>` then clauses terminated by `0`.
    Validates clause count and literal bounds. -/
def parseDimacs (input : String) : Except String DimacsFormula := do
  let tokens := tokenize input (dimacsComments := true)
  -- Find "p" "cnf" header
  let rec findP (pos : Nat) : Nat :=
    if h : pos < tokens.size && tokens[pos]! != "p" then findP (pos + 1) else pos
  termination_by tokens.size - pos
  decreasing_by simp_all; omega
  let pos := findP 0
  if pos + 3 >= tokens.size then
    throw "missing 'p cnf' header"
  if tokens[pos]! != "p" || tokens[pos + 1]! != "cnf" then
    throw "expected 'p cnf' header"
  let numVarsStr := tokens[pos + 2]!
  let numClausesStr := tokens[pos + 3]!
  let numVars ← match numVarsStr.toNat? with
    | some n => pure n
    | none => throw s!"invalid numVars: {numVarsStr}"
  let numClauses ← match numClausesStr.toNat? with
    | some n => pure n
    | none => throw s!"invalid numClauses: {numClausesStr}"
  -- Parse clauses: sequences of integers terminated by 0
  let rec parseClauses (pos : Nat) (clauses : Array DimacsClause) (current : DimacsClause) :
      Array DimacsClause × DimacsClause :=
    if pos < tokens.size then
      let tok := tokens[pos]!
      match tok.toInt? with
      | some 0 => parseClauses (pos + 1) (clauses.push current.reverse) []
      | some n => parseClauses (pos + 1) clauses (n :: current)
      | none => parseClauses (pos + 1) clauses current
    else (clauses, current)
  termination_by tokens.size - pos
  let (clauses, remaining) := parseClauses (pos + 4) #[] []
  if !remaining.isEmpty then
    throw "DIMACS: unterminated clause (missing trailing 0)"
  -- Validate clause count
  if clauses.size != numClauses then
    throw s!"DIMACS clause count mismatch: header declares {numClauses}, found {clauses.size}"
  -- Validate literal bounds
  for clause in clauses do
    for lit in clause do
      let absLit := if lit ≥ 0 then lit.toNat else (-lit).toNat
      -- Note: absLit == 0 check removed (unreachable: parser uses 0 as terminator)
      if absLit > numVars then
        throw s!"DIMACS literal {lit} out of bounds (numVars={numVars})"
  return ⟨numVars, numClauses, clauses⟩


-- Parsed VeriPB proof types

/-- A literal in OPB format: variable name with optional negation. After
parsing, the name is always the canonical `x<idx+1>`. -/
inductive OPBLit where
  | pos : String → OPBLit   -- `x3` → positive literal for variable "x3"
  | neg : String → OPBLit   -- `~x3` → negative literal for variable "x3"
  deriving Repr, BEq

/-- A term in OPB format: coefficient and literal. -/
structure OPBTerm where
  coeff : Nat
  lit : OPBLit
  deriving Repr

/-- An OPB constraint `Σ coeff·lit ≥ degree`: terms and degree. Negative
coefficients and a negative degree are normalized away at parse time. -/
structure OPBConstr where
  terms : List OPBTerm
  degree : Nat
  deriving Repr

/-- An operation in a `pol` RPN sequence. -/
inductive PolOp where
  | pushId (id : Nat)          -- Push constraint by ID
  | pushNat (n : Nat)          -- Push raw integer (for `*` / `d` / `-` operands)
  | pushLitAxiom (l : OPBLit) -- Push literal axiom (l >= 0)
  | add                        -- Pop two, add
  | mul                        -- Pop nat and constraint, multiply
  | div                        -- Pop nat and constraint, divide (ceiling)
  | saturate                   -- Pop one, saturate
  | weaken (varName : String)  -- Pop one, weaken by removing variable
  | lowerRhs                   -- `k -`: pop nat k and constraint, degree - k
  | divVar                     -- `k c`: pop nat k and constraint, variable-form division
  | mir                        -- `k n`: pop nat k and constraint, normalized MIR cut
  | mirVar                     -- `k m`: pop nat k and constraint, variable-form MIR cut
  deriving Repr

/-- A RUP hint: either a constraint ID or `~` (the negated constraint). -/
inductive RupHint where
  | id (n : Nat)   -- Constraint ID
  | negC           -- The `~` symbol: negated target constraint
  deriving Repr, Inhabited

/-- An objective as written in a proof (`eobj`, `obju`): integer
coefficients over literals plus a constant, `Σ coeff·lit + constant`. -/
structure ProofObjective where
  terms : List (Int × OPBLit)
  constant : Int
  deriving Repr

/-- A bound in `conclusion BOUNDS`: an integer or `INF`. -/
inductive Bound where
  | finite (v : Int)
  | inf
  deriving Repr, BEq

/-- `scope leq` / `scope geq` inside a `dom`/`red` subproof. -/
inductive ScopeKind where
  | leq
  | geq
  deriving Repr, BEq

/-- `obju new` / `obju diff`. -/
inductive ObjUpdateKind where
  | new
  | diff
  deriving Repr, BEq

/-- Which strengthening rule a `strengthening` step came from. -/
inductive StrengtheningRule where
  | red
  | dom
  deriving Repr, BEq

/-- Output guarantee other than `NONE` (`output NONE ;` is `ProofStep.output`). -/
inductive OutputGuarantee where
  | derivable
  | equisatisfiable
  | equioptimal
  deriving Repr, BEq

/-- Output type of an `output` statement. -/
inductive OutputKind where
  | file                                     -- `FILE`: formula in a separate file
  | implicit                                 -- `IMPLICIT`
  | permutation (ids : List Nat)             -- `PERMUTATION ids`
  | constraints (objective : Option ProofObjective) (isMax : Bool)
      (constrs : List OPBConstr)             -- `CONSTRAINTS opb ... end`
  deriving Repr

/-- Transitivity block of a `def_order`. -/
structure OrderTransitivity (σ : Type) where
  freshRight : List Nat
  freshAux1 : List Nat
  freshAux2 : List Nat
  /-- Items of `proof ... qed` (usually `proofgoal` steps). -/
  proof : Array σ
  deriving Repr

/-- A `def_order` block. Variables are global variable indices. -/
structure OrderDef (σ : Type) where
  name : String
  left : List Nat
  right : List Nat
  aux : List Nat
  /-- Items of the `spec ... end` block, if present. -/
  spec : Option (Array σ)
  /-- Constraints of the `def ... end` block. -/
  defConstrs : List OPBConstr
  transitivity : Option (OrderTransitivity σ)
  /-- Items of the reflexivity `proof ... qed` block, if present. -/
  reflexivity : Option (Array σ)
  deriving Repr

/-- A proof step in the VeriPB kernel format (the output of
`veripb --elaborate`, VeriPB 3.0.1).

A subproof (of `red`/`dom`, checked `delc`, `obju`) is stored as its item
array plus the optional `qed : id` hint. Items are steps, `proofgoal` steps
and `scope` steps; the last two occur only inside subproofs. -/
inductive ProofStep where
  | formulaSize (n : Nat)                          -- `f N ;`
  | pol (ops : List PolOp)                         -- `pol <RPN> ;`
  | rup (constr : OPBConstr) (hints : List RupHint) -- `rup C : hints ;`
  | ia (constr : OPBConstr) (premise : Option Nat) -- `ia C : id ;`
  | deld (ids : List Nat)                          -- `deld ids ;`
  | delc (ids : List Nat)                          -- `delc ids ;` (unchecked)
  /-- Checked deletion `delc ids : ω [: subproof ... qed [: id]] ;`. -/
  | delcChecked (ids : List Nat) (subst : List (String × String))
      (subproof : Option (Array ProofStep × Option Nat))
  | core (ids : List Nat)                          -- `core id ids ;`
  | coreRange (lo hi : Nat)                        -- `core range lo hi ;` ([lo, hi))
  | strengtheningToCore (on : Bool)                -- `strengthening_to_core on|off ;`
  | pbc (constr : OPBConstr) (steps : Array ProofStep) (resultId : Nat)
  /-- `red C : ω [: subproof ... qed ;]` whose subproof consists of
      `proofgoal` blocks with hints only (or is absent).
      goals: (goalId, inner steps, result constraint id) -/
  | red (constr : OPBConstr) (subst : List (String × String))
        (goals : Array (String × Array ProofStep × Nat))
  /-- `dom C : ω [: subproof ... qed ;]`, same shape restriction as `red`. -/
  | dom (constr : OPBConstr) (subst : List (String × String))
        (goals : Array (String × Array ProofStep × Nat))
  /-- `red`/`dom` with a general subproof: top-level steps, `scope` blocks,
      proofgoals without hint, or a `qed : id` hint. -/
  | strengthening (rule : StrengtheningRule) (constr : OPBConstr)
      (subst : List (String × String)) (items : Array ProofStep)
      (qedHint : Option Nat)
  /-- `proofgoal ID ... qed [: id] ;` (only inside subproofs). -/
  | proofgoal (goalId : String) (steps : Array ProofStep) (hint : Option Nat)
  /-- `scope leq|geq ... end ;` (only inside subproofs). -/
  | scope (kind : ScopeKind) (items : Array ProofStep)
  | defOrder (order : OrderDef ProofStep)          -- `def_order ... end ;`
  | loadOrder (name : Option String) (lits : List OPBLit) -- `load_order [name lits] ;`
  | sol (lits : List OPBLit) (value : Option Int)  -- `sol lits [: v] ;`
  | soli (lits : List OPBLit) (value : Option Int) -- `soli lits [: v] ;`
  | obji (value : Int)                             -- `obji v ;`
  | eobj (obj : ProofObjective)                    -- `eobj f ;`
  /-- `obju new|diff f [: subproof ... qed [: id]] ;` -/
  | obju (kind : ObjUpdateKind) (obj : ProofObjective)
      (subproof : Option (Array ProofStep × Option Nat))
  | output                                         -- `output NONE ;`
  | outputClaim (guarantee : OutputGuarantee) (kind : OutputKind)
  | conclusion (id : Nat)                          -- `conclusion UNSAT : id ;`
  | conclusionSat (lits : Option (List OPBLit))    -- `conclusion SAT [: lits] ;`
  /-- `conclusion BOUNDS lb [: id] ub [: lits] ;` -/
  | conclusionBounds (lb : Bound) (lbHint : Option Nat) (ub : Bound)
      (ubLits : Option (List OPBLit))
  | conclusionNone                                 -- `conclusion NONE ;`
  deriving Repr

/-- A complete parsed VeriPB kernel proof. `numVars` is the variable count
after the proof's fresh variables were added, `names` the full name table
(non-`x<N>` names with their indices). -/
structure VeriPBProof where
  steps : Array ProofStep
  numVars : Nat := 0
  names : List (String × Nat) := []
  deriving Repr

-- OPB constraint parser

/-- Parse a variable name from a token. Returns the variable name (without ~).
    Tokens like "x3" → pos "x3", "~x3" → neg "x3". -/
def parseOPBLit (tok : String) : Except String OPBLit :=
  if tok.startsWith "~" then
    let varName := (tok.drop 1).toString
    if varName.isEmpty then
      throw "empty variable name after ~"
    else
      .ok (.neg varName)
  else
    if tok.isEmpty then
      throw "empty variable name"
    else
      .ok (.pos tok)

/-- Convert a variable name like "x3" to a 0-based variable index. -/
def varNameToIdx (varName : String) : Except String Nat :=
  if varName.startsWith "x" then
    match (varName.drop 1).toString.toNat? with
    | some n => if n > 0 then .ok (n - 1)
                else .error "variable index must be > 0"
    | none => .error s!"invalid variable name: {varName}"
  else .error s!"expected variable name starting with 'x', got: {varName}"

/-- Convert raw substitution string pairs to kernel-level (Nat x SubstVal). -/
def parseSubstPairs (pairs : List (String × String)) (numVars : Nat) :
    Except String (List (Nat × Sat.PB.SubstVal)) :=
  let rec go (remaining : List (String × String))
      (seen : Std.HashSet Nat) (acc : List (Nat × Sat.PB.SubstVal)) :
      Except String (List (Nat × Sat.PB.SubstVal)) :=
    match remaining with
    | [] => .ok acc
    | (varStr, valStr) :: rest => do
      let varIdx ← varNameToIdx varStr
      if varIdx >= numVars then
        .error s!"substitution variable {varStr} (index {varIdx}) out of range \
          (numVars={numVars})"
      else
        let sv : Sat.PB.SubstVal ←
          if valStr == "0" then .ok .zero
          else if valStr == "1" then .ok .one
          else match parseOPBLit valStr with
          | .ok (.pos vn) => do
            let j ← varNameToIdx vn
            if j >= numVars then
              .error s!"substitution target {vn} (index {j}) out of range \
                (numVars={numVars})"
            else .ok (.posLit j)
          | .ok (.neg vn) => do
            let j ← varNameToIdx vn
            if j >= numVars then
              .error s!"substitution target ~{vn} (index {j}) out of range \
                (numVars={numVars})"
            else .ok (.negLit j)
          | .error e => .error s!"invalid substitution value '{valStr}': {e}"
        -- a repeated entry with the same target is ignored, a conflicting one is
        -- an error (CakePB; VeriPB keeps the first)
        match Sat.PB.lookupSubst acc varIdx with
        | some sv' =>
          if sv' == sv then go rest seen acc
          else .error s!"conflicting substitutions for variable {varStr} (index {varIdx})"
        | none => go rest (seen.insert varIdx) (acc ++ [(varIdx, sv)])
  go pairs ∅ []

/-- Parse a coefficient string like "+1", "3", "-2" into an Int.
    Supports both positive and negative coefficients. -/
def parseCoeffInt (tok : String) : Except String Int :=
  match intTokenVal? tok with
  | some n => .ok n
  | none => .error s!"invalid coefficient: {tok}"

/-- Negate an OPB literal. -/
def OPBLit.negate : OPBLit → OPBLit
  | .pos name => .neg name
  | .neg name => .pos name


/-! ### Proof parser

The grammar follows VeriPB 3.0.1 (`src/parser/parser.rs`, rule dispatch in
`Parser::rule`) restricted to the statements that `veripb --elaborate`
writes (`elaborate()` in `src/rules/*.rs`). -/

/-- If the token is a literal (`name` or `~name`) by its spelling, resolve
the variable with `resolveVarIdx` and return the literal in canonical form;
otherwise `none`. -/
def parseLitTok? (tok : String) : ParseM (Option OPBLit) := do
  -- 126 = '~'
  let neg := byteAt tok 0 == 126
  let cx := canonXIndexAt? tok (if neg then 1 else 0)
  let name := if neg then (tok.drop 1).toString else tok
  if cx.isNone && !isVarName name then return none
  let i ← resolveVarIdx name cx
  -- an `x<N>` name is already canonical; reuse the string
  let canon := if cx.isSome then name else canonVarName i
  return some (if neg then .neg canon else .pos canon)

/-- Parse a literal token `name` or `~name`; the variable is resolved with
`resolveVar` and written in canonical form. -/
def parseLitTok (tok : String) : ParseM OPBLit := do
  match ← parseLitTok? tok with
  | some l => return l
  | none => throw s!"expected a literal, got '{tok}'"

/-- `Σ cᵢ·lᵢ ≥ d` with integer coefficients and degree, normalized to
nonnegative coefficients (`-a·l ≡ a·~l - a`) and a degree clamped at `0`
(a constraint `Σ ≥ d` with `d ≤ 0` over a nonnegative sum is trivially
true, as is `Σ ≥ 0`). -/
def mkGeqConstr (terms : List (Int × OPBLit)) (degree : Int) : OPBConstr :=
  let (ts, adj) := terms.foldl (init := (([] : List OPBTerm), (0 : Int)))
    fun (acc, adj) (c, l) =>
      if c ≥ 0 then (⟨c.toNat, l⟩ :: acc, adj)
      else (⟨(-c).toNat, l.negate⟩ :: acc, adj - c)
  ⟨ts.reverse, (degree + adj).toNat⟩

/-- Parse `c₁ l₁ c₂ l₂ ...` up to (not including) a token in `stops`. -/
def parseIntTerms (stops : List String) : ParseM (List (Int × OPBLit)) := do
  let mut terms : List (Int × OPBLit) := []
  while !stops.contains (← peek) do
    let c ← parseInt
    let lit ← parseLitTok (← next)
    terms := (c, lit) :: terms
  return terms.reverse

/-- Parse a proof constraint `c₁ l₁ ... ≥ d` (the form VeriPB's elaborator
writes; `d` may be negative). Also handles the empty left-hand side. -/
def parseOPBConstr : ParseM OPBConstr := do
  let terms ← parseIntTerms [">="]
  expect ">="
  let degree ← parseInt
  return mkGeqConstr terms degree

/-- Parse an OPB constraint with relation `>=`, `<=` or `=` and the final
`;` (used in `def` blocks and `CONSTRAINTS` listings). Returns the `≥`
part first, then the `≤` part, as VeriPB's `generate_constraints` does. -/
def parseRelConstr : ParseM (List OPBConstr) := do
  if (← peek).startsWith "@" then let _ ← next  -- optional label
  let terms ← parseIntTerms [">=", "<=", "="]
  let rel ← next
  let degree ← parseInt
  expectSemicolon
  let geq := mkGeqConstr terms degree
  let leq := mkGeqConstr (terms.map fun (c, l) => (-c, l)) (-degree)
  match rel with
  | ">=" => return [geq]
  | "<=" => return [leq]
  | _ => return [geq, leq]

/-- Parse the RPN operations for a `pol` step (VeriPB `pol_rule`).
Tokens are consumed until `;`. A number directly before `*`, `d` or `-` is
an integer operand, every other number a constraint ID; `w` consumes the
variable that precedes it (`x3 w`). `c` is division in variable form, `n`
and `m` are the normalized and variable-form mixed-integer rounding cuts;
a number directly before them is their integer operand. -/
def parsePolOps : ParseM (List PolOp) := do
  let mut ops : List PolOp := []
  while (← peek) != ";" do
    let tok ← next
    if tok == "+" then
      ops := .add :: ops
    else if tok == "-" then
      ops := .lowerRhs :: ops
    else if tok == "s" then
      ops := .saturate :: ops
    else if tok == "*" then
      ops := .mul :: ops
    else if tok == "d" then
      ops := .div :: ops
    else if tok == "c" then
      ops := .divVar :: ops
    else if tok == "n" then
      ops := .mir :: ops
    else if tok == "m" then
      ops := .mirVar :: ops
    else if tok == "w" then
      match ops with
      | .pushLitAxiom (.pos varName) :: rest => ops := .weaken varName :: rest
      | _ => throw "weakening: expected a variable before 'w'"
    else
      match ← parseLitTok? tok with
      | some lit => ops := .pushLitAxiom lit :: ops
      | none =>
        match natTokenVal? tok with
        | some n =>
          let nextTok ← peek
          if nextTok == "*" || nextTok == "d" || nextTok == "-" ||
              nextTok == "c" || nextTok == "n" || nextTok == "m" then
            ops := .pushNat n :: ops
          else
            ops := .pushId n :: ops
        | none => throw s!"unexpected token in pol: '{tok}'"
  return ops.reverse

/-- Parse RUP hints: list of constraint IDs and/or `~`, terminated by `;`. -/
def parseRupHints : ParseM (List RupHint) := do
  let mut hints : List RupHint := []
  while (← peek) != ";" do
    let tok ← next
    if tok == "~" then
      hints := .negC :: hints
    else
      match natTokenVal? tok with
      | some n => hints := .id n :: hints
      | none => throw s!"unexpected RUP hint: '{tok}'"
  return hints.reverse

/-- Parse a list of constraint IDs up to `;` or `:` (not consumed). -/
def parseIdList : ParseM (List Nat) := do
  let mut ids : List Nat := []
  while (← peek) != ";" && (← peek) != ":" do
    let n ← parseNat
    ids := n :: ids
  return ids.reverse

/-- Parse solution literals up to `;` or `:` (not consumed). -/
def parseSolLits : ParseM (List OPBLit) := do
  let mut lits : List OPBLit := []
  while (← peek) != ";" && (← peek) != ":" do
    lits := (← parseLitTok (← next)) :: lits
  return lits.reverse

/-- Parse a witness `v₁ -> a₁ v₂ -> a₂ ...` (VeriPB `witness`; the arrow
may be omitted) up to and including the closing `:` or `;`, which is
returned. Values are `0`, `1` or a literal. -/
def parseWitness : ParseM (List (String × String) × String) := do
  let mut pairs : List (String × String) := []
  let mut tok ← next
  while tok != ":" && tok != ";" do
    if tok.startsWith "~" then
      throw s!"witness: expected a variable, got '{tok}'"
    let i ← resolveVar tok
    let _ ← accept "->"
    let valTok ← next
    let val ← if valTok == "0" || valTok == "1" then pure valTok
      else match ← parseLitTok valTok with
        | .pos n => pure n
        | .neg n => pure ("~" ++ n)
    pairs := (canonVarName i, val) :: pairs
    tok ← next
  return (pairs.reverse, tok)

/-- Parse an objective `c₁ l₁ ... [k]` (VeriPB `objective`) up to `;` or
`:` (not consumed): coefficient-literal pairs and an optional trailing
constant. -/
def parseObjective : ParseM ProofObjective := do
  let mut terms : List (Int × OPBLit) := []
  let mut constant : Int := 0
  let mut nonempty := false
  while (← peek) != ";" && (← peek) != ":" do
    let c ← parseInt
    nonempty := true
    let t ← peek
    if t == ";" || t == ":" then
      constant := c
    else
      terms := (c, ← parseLitTok (← next)) :: terms
  if !nonempty then throw "objective: expected a coefficient"
  return ⟨terms.reverse, constant⟩

/-- Parse a bound: a signed integer or `INF`. -/
def parseBound : ParseM Bound := do
  if (← peek) == "INF" then
    let _ ← next
    return .inf
  return .finite (← parseInt)

/-- After `qed` (and an optional repeated keyword): `;` or `: id ;`. -/
def parseQedHint : ParseM (Option Nat) := do
  if ← accept ";" then return none
  expect ":"
  let id ← parseNat
  expectSemicolon
  return some id

/-- Declared variables up to and including `;` (order `vars` blocks). A new
name gets a fresh index. -/
def parseVarDecls : ParseM (List Nat) := withFresh do
  let mut vs : List Nat := []
  while (← peek) != ";" do
    vs := (← resolveVar (← next)) :: vs
  expectSemicolon
  return vs.reverse

/-- Where a statement occurs (VeriPB `Scope`); decides whether `proofgoal`
and `scope` are allowed. -/
inductive StepCtx where
  | top | subproof | scope | proofgoal | proof | spec
  deriving BEq, Inhabited

/-- A `red` step (either constructor): the only statement allowed in the
`spec` block of a `def_order`. -/
def isSpecRedStep : ProofStep → Bool
  | .red .. | .strengthening .red .. => true
  | _ => false

/-- `red`/`dom` with an optional subproof. A subproof that consists of
`proofgoal` blocks with hints and ends with a plain `qed ;` gives the
`red`/`dom` constructor, every other subproof `strengthening`. -/
def mkStrengthening (rule : StrengtheningRule) (constr : OPBConstr)
    (subst : List (String × String))
    (sub : Option (Array ProofStep × Option Nat)) : ProofStep :=
  let simple (goals : Array (String × Array ProofStep × Nat)) : ProofStep :=
    match rule with
    | .red => .red constr subst goals
    | .dom => .dom constr subst goals
  match sub with
  | none => simple #[]
  | some (items, none) =>
    match items.mapM (fun s => match s with
        | .proofgoal gid steps (some h) => some (gid, steps, h)
        | _ => none) with
    | some goals => simple goals
    | none => .strengthening rule constr subst items none
  | some (items, hint) => .strengthening rule constr subst items hint

mutual

/-- Parse statements until the token `stop` (not consumed). -/
partial def parseItems (ctx : StepCtx) (stop : String) :
    ParseM (Array ProofStep) := do
  let mut items : Array ProofStep := #[]
  while (← peek) != stop do
    items := items.push (← parseStep ctx)
  return items

/-- After the `subproof` keyword: items up to `qed`, then `qed [rule]`
followed by `;` or `: id ;` (VeriPB `subproof`, `subproof_qed`). -/
partial def parseSubproof (rule : String) :
    ParseM (Array ProofStep × Option Nat) := do
  let _ ← accept ";"  -- lenient: `subproof ;`
  let items ← parseItems .subproof "qed"
  expect "qed"
  let _ ← accept rule
  let hint ← parseQedHint
  return (items, hint)

/-- `proof ... qed [proof] ;` inside `def_order` (VeriPB `order_proof`). -/
partial def parseOrderProof : ParseM (Array ProofStep) := do
  expect "proof"
  let items ← parseItems .proof "qed"
  expect "qed"
  let _ ← accept "proof"
  expectSemicolon
  return items

/-- Parse the body of `def_order NAME` (VeriPB `def_order_rule`). -/
partial def parseDefOrder (name : String) : ParseM (OrderDef ProofStep) := do
  expect "vars"
  expect "left"
  let left ← parseVarDecls
  expect "right"
  let right ← parseVarDecls
  let aux ← if ← accept "aux" then parseVarDecls else pure []
  expect "end"
  let _ ← accept "vars"
  expectSemicolon
  let spec ← if ← accept "spec" then do
      let items ← parseItems .spec "end"
      -- CakePB `parse_spec_aux`: only `red` steps (VeriPB accepts any rule)
      if !items.all isSpecRedStep then
        throw "def_order: a spec block may contain only red steps"
      expect "end"
      let _ ← accept "spec"
      expectSemicolon
      pure (some items)
    else pure none
  expect "def"
  let mut defConstrs : List OPBConstr := []
  while (← peek) != "end" do
    -- VeriPB `single_constraint`: the `≥` part, or the `≤` part for `<=`;
    -- `=` is rejected (VeriPB `order_def_constraint`, CakePB `parse_def_aux`)
    match ← parseRelConstr with
    | [c] => defConstrs := defConstrs ++ [c]
    | _ => throw "def_order: '=' is not allowed in a def block"
  expect "end"
  let _ ← accept "def"
  expectSemicolon
  let transitivity ← if ← accept "transitivity" then do
      expect "vars"
      expect "fresh_right"
      let freshRight ← parseVarDecls
      let (freshAux1, freshAux2) ← if ← accept "fresh_aux_1" then do
          let a1 ← parseVarDecls
          expect "fresh_aux_2"
          let a2 ← parseVarDecls
          pure (a1, a2)
        else pure ([], [])
      expect "end"
      let _ ← accept "vars"
      expectSemicolon
      let proof ← parseOrderProof
      expect "end"
      let _ ← accept "transitivity"
      expectSemicolon
      pure (some { freshRight, freshAux1, freshAux2, proof : OrderTransitivity ProofStep })
    -- both blocks are mandatory (CakePB `parse_trans_refl_block`; VeriPB
    -- cannot autoprove transitivity and its elaborator always writes both)
    else throw "def_order: missing transitivity block"
  let reflexivity ← if ← accept "reflexivity" then do
      let proof ← parseOrderProof
      expect "end"
      let _ ← accept "reflexivity"
      expectSemicolon
      pure (some proof)
    else throw "def_order: missing reflexivity block"
  expect "end"
  let _ ← accept "def_order"
  expectSemicolon
  return { name, left, right, aux, spec, defConstrs, transitivity, reflexivity }

/-- Parse a single proof step. -/
partial def parseStep (ctx : StepCtx) : ParseM ProofStep := do
  let keyword ← next
  match keyword with
  | "f" =>
    let n ← parseNat
    expectSemicolon
    return .formulaSize n
  | "pol" =>
    let ops ← parsePolOps
    expectSemicolon
    return .pol ops
  | "rup" =>
    let constr ← parseOPBConstr
    if ← accept ";" then return .rup constr []
    expect ":"
    let hints ← parseRupHints
    expectSemicolon
    return .rup constr hints
  | "ia" =>
    let constr ← parseOPBConstr
    if ← accept ";" then return .ia constr none
    expect ":"
    let id ← parseNat
    expectSemicolon
    return .ia constr (some id)
  | "deld" =>
    let ids ← parseIdList
    expectSemicolon
    return .deld ids
  | "delc" =>
    let ids ← parseIdList
    if ← accept ";" then return .delc ids
    expect ":"
    let (subst, endTok) ← withFresh parseWitness
    if endTok == ";" then return .delcChecked ids subst none
    expect "subproof"
    let sp ← parseSubproof "delc"
    return .delcChecked ids subst (some sp)
  | "core" =>
    match ← next with
    | "id" =>
      let ids ← parseIdList
      expectSemicolon
      return .core ids
    | "range" =>
      let lo ← parseNat
      let hi ← parseNat
      expectSemicolon
      return .coreRange lo hi
    | t => throw s!"core: expected 'id' or 'range', got '{t}'"
  | "strengthening_to_core" =>
    let on ← match ← next with
      | "on" => pure true
      | "off" => pure false
      | t => throw s!"strengthening_to_core: expected 'on' or 'off', got '{t}'"
    expectSemicolon
    return .strengtheningToCore on
  | "output" =>
    let g ← next
    if g == "NONE" then
      expectSemicolon
      return .output
    let guarantee ← match g with
      | "DERIVABLE" => pure OutputGuarantee.derivable
      | "EQUISATISFIABLE" => pure .equisatisfiable
      | "EQUIOPTIMAL" => pure .equioptimal
      | _ => throw s!"unknown output guarantee: {g}"
    match ← next with
    | "FILE" =>
      expectSemicolon
      return .outputClaim guarantee .file
    | "IMPLICIT" =>
      expectSemicolon
      return .outputClaim guarantee .implicit
    | "PERMUTATION" =>
      let ids ← parseIdList
      expectSemicolon
      return .outputClaim guarantee (.permutation ids)
    | "CONSTRAINTS" =>
      expect "opb"
      let mut objective : Option ProofObjective := none
      let mut isMax := false
      let t ← peek
      if t == "min:" || t == "max:" || t == "min" || t == "max" then
        let _ ← next
        isMax := t.startsWith "max"
        if t == "min" || t == "max" then expect ":"
        objective := some (← parseObjective)
        expectSemicolon
      let mut constrs : List OPBConstr := []
      while (← peek) != "end" do
        constrs := constrs ++ (← parseRelConstr)
      expect "end"
      let _ ← accept "opb"
      expectSemicolon
      return .outputClaim guarantee (.constraints objective isMax constrs)
    | t => throw s!"unknown output type: {t}"
  | "conclusion" =>
    let kind ← next
    match kind with
    | "UNSAT" =>
      expect ":"
      let id ← parseNat
      expectSemicolon
      return .conclusion id
    | "SAT" =>
      if ← accept ";" then return .conclusionSat none
      expect ":"
      let lits ← parseSolLits
      expectSemicolon
      -- `conclusion SAT : ;` is the all-false assignment, as in CakePB
      -- (`parse_assg [] = SOME []`); VeriPB reads it as no hint
      return .conclusionSat (some lits)
    | "BOUNDS" =>
      let lb ← parseBound
      let lbHint ← if ← accept ":" then some <$> parseNat else pure none
      let ub ← parseBound
      -- `ub : ;` is the all-false assignment, as in CakePB
      -- (`parse_assg [] = SOME []`); VeriPB reads it as no hint
      let ubLits ← if ← accept ":" then some <$> parseSolLits else pure none
      expectSemicolon
      return .conclusionBounds lb lbHint ub ubLits
    | "NONE" =>
      expectSemicolon
      return .conclusionNone
    | _ => throw s!"unknown conclusion type: {kind}"
  | "sol" | "soli" =>
    -- VeriPB adds unknown names of a logged solution as new variables
    -- (`sol_common` → `literals` → `VarNameManager::add_by_name`).
    let lits ← withFresh parseSolLits
    let value ← if ← accept ":" then some <$> parseInt else pure none
    expectSemicolon
    return if keyword == "sol" then .sol lits value else .soli lits value
  | "obji" =>
    let v ← parseInt
    expectSemicolon
    return .obji v
  | "eobj" =>
    let obj ← parseObjective
    expectSemicolon
    return .eobj obj
  | "obju" =>
    let kind ← match ← next with
      | "new" => pure ObjUpdateKind.new
      | "diff" => pure .diff
      | t => throw s!"obju: expected 'new' or 'diff', got '{t}'"
    let obj ← parseObjective
    if ← accept ";" then return .obju kind obj none
    expect ":"
    expect "subproof"
    let sp ← parseSubproof "obju"
    return .obju kind obj (some sp)
  | "pbc" =>
    let constr ← parseOPBConstr
    expect ":"
    expect "subproof"
    let _ ← accept ";"  -- semicolon after 'subproof' is optional
    let innerSteps ← parseItems .subproof "qed"
    expect "qed"
    let _ ← accept "pbc"
    expect ":"
    let resultId ← parseNat
    expectSemicolon
    return .pbc constr innerSteps resultId
  | "red" | "dom" =>
    let rule := if keyword == "red" then StrengtheningRule.red else .dom
    -- A name first seen in the constraint or the witness is a fresh
    -- (extension) variable.
    let constr ← withFresh parseOPBConstr
    if ← accept ";" then return mkStrengthening rule constr [] none
    expect ":"
    let (subst, endTok) ← withFresh parseWitness
    if endTok == ";" then return mkStrengthening rule constr subst none
    let kw ← next
    if kw != "subproof" && kw != "begin" then
      throw s!"expected 'subproof' in {keyword} step, got '{kw}'"
    let sp ← parseSubproof keyword
    return mkStrengthening rule constr subst (some sp)
  | "proofgoal" =>
    if !(ctx == .subproof || ctx == .scope || ctx == .proof) then
      throw "'proofgoal' outside a subproof"
    let goalId ← next
    let isHash := goalId.startsWith "#" && isDecDigits (goalId.drop 1).toString
    if !isHash && !isDecDigits goalId then
      throw s!"invalid proofgoal ID '{goalId}'"
    let steps ← parseItems .proofgoal "qed"
    expect "qed"
    let _ ← accept goalId
    let hint ← parseQedHint
    return .proofgoal goalId steps hint
  | "scope" =>
    if ctx != .subproof then
      throw "'scope' outside a subproof"
    let kind ← match ← next with
      | "leq" => pure ScopeKind.leq
      | "geq" => pure .geq
      | t => throw s!"scope: expected 'leq' or 'geq', got '{t}'"
    let items ← parseItems .scope "end"
    expect "end"
    let _ ← accept "scope"
    expectSemicolon
    return .scope kind items
  | "def_order" =>
    let name ← next
    return .defOrder (← parseDefOrder name)
  | "load_order" =>
    if ← accept ";" then return .loadOrder none []
    let name ← next
    let lits ← parseSolLits
    expectSemicolon
    return .loadOrder (some name) lits
  | other => throw s!"unknown proof step keyword: '{other}'"

end

/-- Parse a complete VeriPB kernel proof. `vt` holds the input formula's
named variables and variable count (see the module doc). -/
def parseVeriPBProofWith (vt : VarTable) (input : String) :
    Except String VeriPBProof := do
  let tokens := tokenize input
  -- Fresh names get indices above every `x<N>` of the proof, so that a name
  -- declared early never takes the index of an `x<N>` that appears later.
  -- A proof cannot introduce more variables than it has tokens, so every
  -- index must be below `vt.numVars + tokens.size`; a larger `x<N>` would
  -- only make the checker allocate arrays of that size.
  let varBound := vt.numVars + tokens.size
  let mut maxX := vt.numVars
  for t in tokens do
    -- 126 = '~', 120 = 'x'
    let off := if byteAt t 0 == 126 then 1 else 0
    if byteAt t off == 120 then
      if let some i := canonXIndexAt? t off then
        if i ≥ varBound then
          throw s!"variable index of '{t}' too large (the proof has {tokens.size} tokens)"
        maxX := max maxX (i + 1)
  let initState : ParseState :=
    { tokens, pos := 0, vars := { vt with numVars := maxX }, varBound }
  let parseAll : ParseM VeriPBProof := do
    expect "pseudo-Boolean"
    expect "proof"
    expect "version"
    expect "3.0"
    let mut steps : Array ProofStep := #[]
    while (← peek) != "end" do
      let step ← parseStep .top
      steps := steps.push step
    expect "end"
    expect "pseudo-Boolean"
    expect "proof"
    expectSemicolon
    let s ← get
    return { steps, numVars := s.vars.numVars, names := s.vars.toList }
  match parseAll initState with
  | .ok result _ => .ok result
  | .error e s => .error s!"{e} (at token {s.pos})"

/-- Parse a proof whose formula has only `x<N>` variables. -/
def parseVeriPBProof (input : String) : Except String VeriPBProof :=
  parseVeriPBProofWith {} input

-- Variable name mapping (for CNF → PB bridge)

/-- Convert OPBLit to Sat.PB.Literal using DIMACS naming convention.
    Variable "xN" maps to PB variable (N-1) (0-indexed). -/
def opbLitToPB (lit : OPBLit) : Except String Sat.PB.Literal :=
  let extractVar (name : String) : Except String Nat :=
    if name.startsWith "x" then
      match (name.drop 1).toString.toNat? with
      | some n => if n > 0 then .ok (n - 1) else .error "variable index must be > 0"
      | none => .error s!"invalid variable name: {name}"
    else
      .error s!"expected variable name starting with 'x', got: {name}"
  match lit with
  | .pos name => do
    let idx ← extractVar name
    return .pos idx
  | .neg name => do
    let idx ← extractVar name
    return .neg idx

/-- Convert an OPBConstr to a Sat.PB.Constr. -/
def opbConstrToPB (c : OPBConstr) : Except String Sat.PB.Constr := do
  let terms ← c.terms.mapM fun t => do
    let lit ← opbLitToPB t.lit
    return (t.coeff, lit)
  return ⟨terms, c.degree⟩

-- Constraint operations (normalization, cutting planes) on `Sat.PB.Constr`

/-- Merge like terms and remove zero-coefficient terms. -/
def mergeLikeTerms (terms : List Sat.PB.Term) : List Sat.PB.Term :=
  let rec go (acc : List Sat.PB.Term) : List Sat.PB.Term → List Sat.PB.Term
    | [] => acc.reverse
    | (c, l) :: rest =>
      match acc.find? fun (_, l') => l' == l with
      | some _ =>
        let acc' := acc.map fun (c'', l') => if l' == l then (c'' + c, l') else (c'', l')
        go acc' rest
      | none => go ((c, l) :: acc) rest
  (go [] terms).filter fun (c, _) => c != 0

/-- Find the index of the first zero-coefficient term. -/
def findZeroIdx (terms : List Sat.PB.Term) : Option Nat :=
  terms.findIdx? fun (c, _) => c == 0

/-- Find indices of the first complementary pair where
`min a b ≤ degree` (required by `cancel_pair_sat`). -/
def findValidCompPairIdx (terms : List Sat.PB.Term) (degree : Nat) : Option (Nat × Nat) :=
  let rec go (i : Nat) : List Sat.PB.Term → Option (Nat × Nat)
    | [] => none
    | (a, l) :: rest =>
      match rest.findIdx? fun (_, l') => l' == l.negate with
      | some offset =>
        let j := i + 1 + offset
        let (b, _) := terms[j]!
        if min a b ≤ degree then some (i, j)
        else go (i + 1) rest
      | none => go (i + 1) rest
  go 0 terms

/-- Find indices of the first pair of terms with the same literal (not complement). -/
def findLikeTermIdx (terms : List Sat.PB.Term) : Option (Nat × Nat) :=
  let rec go (i : Nat) : List Sat.PB.Term → Option (Nat × Nat)
    | [] => none
    | (_, l) :: rest =>
      match rest.findIdx? fun (_, l') => l' == l with
      | some offset => some (i, i + 1 + offset)
      | none => go (i + 1) rest
  go 0 terms

/-- Normalization fuel: each cancel-pair step may produce a zero needing removal
    (2 fuel per pair), plus zeros and like-term merges. 4 * length + 1 is safe. -/
def normFuel (nTerms : Nat) : Nat := 4 * nTerms + 1

-- Exact array-based simulation of `normalizeConstr` (used at runtime via
-- @[implemented_by], and by the fast reflection checker in ReflectFast.lean).
-- Literal codes: `2*v` for `x_v`, `2*v+1` for `¬x_v`.

/-- General exact simulation of `normalizeConstr.go` on arrays with the same
priorities (drop first zero; cancel the first complementary pair whose
`min ≤ degree`; merge the first like-term pair) and O(n²) scans. Only used
by `normalizeArrays` when its one-pass fast path meets a cancellation that
is blocked by the degree guard (which can happen only for trivially
satisfied constraints) or when the literal codes are too sparse for the
scratch arrays; also called directly by `Tests/Normalize.lean`. -/
def normalizeArraysGeneral (coeffs lits : Array Nat) (degree : Nat) :
    Array Nat × Array Nat × Nat := Id.run do
  let mut cs := coeffs
  let mut ls := lits
  let mut deg := degree
  let mut fuel := 4 * cs.size + 1
  while fuel > 0 do
    fuel := fuel - 1
    let n := cs.size
    match cs.findIdx? (· == 0) with
    | some idx =>
      cs := cs.eraseIdxIfInBounds idx
      ls := ls.eraseIdxIfInBounds idx
    | none =>
      let mut found : Option (Nat × Nat) := none
      let mut i := 0
      while i < n && found.isNone do
        let comp := ls[i]! ^^^ 1
        let mut j := i + 1
        while j < n && ls[j]! != comp do j := j + 1
        if j < n then
          if min cs[i]! cs[j]! ≤ deg then found := some (i, j)
        i := i + 1
      match found with
      | some (pi, pj) =>
        let m := min cs[pi]! cs[pj]!
        cs := cs.set! pi (cs[pi]! - m)
        cs := cs.set! pj (cs[pj]! - m)
        deg := deg - m
      | none =>
        let mut foundL : Option (Nat × Nat) := none
        let mut i2 := 0
        while i2 < n && foundL.isNone do
          let l := ls[i2]!
          let mut j := i2 + 1
          while j < n && ls[j]! != l do j := j + 1
          if j < n then foundL := some (i2, j)
          i2 := i2 + 1
        match foundL with
        | some (qi, qj) =>
          cs := cs.set! qi (cs[qi]! + cs[qj]!)
          cs := cs.eraseIdxIfInBounds qj
          ls := ls.eraseIdxIfInBounds qj
        | none => fuel := 0
  return (cs, ls, deg)

/-- Exact simulation of `normalizeConstr` on parallel arrays (coefficients,
literal codes), in O(n + maxLit) time where `maxLit` is the largest literal
code. Returns the normalized arrays and degree, in the same term order as
the verified definition, and a flag that is `true` iff the one-pass fast
path completed, in which case the result is a *block* (no zero
coefficient, no repeated literal, no complementary pair).

Phase A drops zero coefficients. Phase B replays the verified cancellation
process (for position `i`, the first later complement `j`; cancel
`min` if `min ≤ degree`) in one forward pass. As long as no cancellation
has been blocked by the degree guard, a cancellation at `i` cannot create
a complementary pair for an earlier position, so the verified restart from
position 0 is equivalent to re-examining `i`. When a blocked pair is met,
`normalizeArraysGeneral` continues from the current state. Phase C merges
like terms into their first occurrence, which is what the verified loop does
once no cancellable pair remains. When the literal codes are sparse
relative to the term count (`maxLit + 2 > n² + 8`), the O(n²) general
algorithm is used directly instead of allocating the scratch arrays.
Property-tested against a verbatim copy of `normalizeConstr`
(`Tests/Normalize.lean`). -/
def normalizeArraysCore (coeffs lits : Array Nat) (degree : Nat) :
    Array Nat × Array Nat × Nat × Bool := Id.run do
  let n0 := coeffs.size
  -- Phase A: drop zeros, find the largest literal code
  let mut cs : Array Nat := Array.mkEmpty n0
  let mut ls : Array Nat := Array.mkEmpty n0
  let mut maxLit := 0
  for k in [:n0] do
    let a := coeffs[k]!
    if a != 0 then
      let l := lits[k]!
      cs := cs.push a
      ls := ls.push l
      if l > maxLit then maxLit := l
  let n := cs.size
  let L := maxLit + 2
  if L > n * n + 8 then
    let (cs', ls', d') := normalizeArraysGeneral cs ls degree
    return (cs', ls', d', false)
  -- Occurrence chains: head[l] = first position holding literal l,
  -- nextSame[p] = next position holding the same literal; n = none.
  let mut head : Array Nat := Array.replicate L n
  let mut nextSame : Array Nat := Array.replicate n n
  for k in [:n] do
    let p := n - 1 - k
    let l := ls[p]!
    nextSame := nextSame.set! p head[l]!
    head := head.set! l p
  -- Phase B: sequential cancellation, one forward pass
  let mut deg := degree
  let mut i := 0
  let mut blocked := false
  while i < n && !blocked do
    let a := cs[i]!
    if a == 0 then
      i := i + 1
    else
      let comp := ls[i]! ^^^ 1
      -- first live occurrence of the complement after i; positions before i
      -- and dead positions can be skipped permanently since i only grows
      let mut j := head[comp]!
      while j < n && (j < i || cs[j]! == 0) do
        j := nextSame[j]!
      head := head.set! comp j
      if j ≥ n then
        i := i + 1
      else
        let b := cs[j]!
        let m := min a b
        if m ≤ deg then
          cs := cs.set! i (a - m)
          cs := cs.set! j (b - m)
          deg := deg - m
        else
          blocked := true
  if blocked then
    let (cs', ls', d') := normalizeArraysGeneral cs ls deg
    return (cs', ls', d', false)
  -- Phase C: merge like terms into their first occurrence
  let mut slot : Array Nat := Array.replicate L n
  let mut outC : Array Nat := Array.mkEmpty n
  let mut outL : Array Nat := Array.mkEmpty n
  for p in [:n] do
    let a := cs[p]!
    if a != 0 then
      let l := ls[p]!
      let s := slot[l]!
      if s == n then
        slot := slot.set! l outC.size
        outC := outC.push a
        outL := outL.push l
      else
        outC := outC.set! s (outC[s]! + a)
  return (outC, outL, deg, true)

/-- `normalizeArraysCore` without the block flag. -/
def normalizeArrays (coeffs lits : Array Nat) (degree : Nat) :
    Array Nat × Array Nat × Nat :=
  let (cs, ls, d, _) := normalizeArraysCore coeffs lits degree
  (cs, ls, d)

/-- Literal code used by `normalizeArrays`: `2*v` positive, `2*v+1` negative. -/
@[inline] def litCode : Sat.PB.Literal → Nat
  | .pos v => 2 * v
  | .neg v => 2 * v + 1

/-- Inverse of `litCode`. -/
@[inline] def litOfCode (l : Nat) : Sat.PB.Literal :=
  if l % 2 == 0 then .pos (l / 2) else .neg (l / 2)

-- Runtime implementation of `normalizeConstr` (exact, see `normalizeArrays`).
private def normalizeConstrFast (c : Sat.PB.Constr) : Sat.PB.Constr :=
  let ts := c.terms.toArray
  let (cs, ls, d) := normalizeArrays (ts.map (·.1)) (ts.map (litCode ·.2)) c.degree
  let terms := (List.range cs.size).map fun i => (cs[i]!, litOfCode ls[i]!)
  ⟨terms, d⟩

/-- Normalize a PB constraint: remove zeros, cancel complementary pairs (with
    `min a b ≤ degree` guard matching Expr-level `buildNormalization`), merge like terms.
    Uses the same iterative approach as the metaprogram layer to ensure consistency. -/
@[implemented_by normalizeConstrFast]
def normalizeConstr (c : Sat.PB.Constr) : Sat.PB.Constr :=
  let rec go (fuel : Nat) (terms : List Sat.PB.Term) (degree : Nat) : Sat.PB.Constr :=
    match fuel with
    | 0 => ⟨terms, degree⟩
    | n + 1 =>
      -- Priority 1: remove zero-coefficient terms
      match findZeroIdx terms with
      | some idx =>
        let pre := terms.take idx
        let post := terms.drop (idx + 1)
        go n (pre ++ post) degree
      | none =>
        -- Priority 2: cancel complementary pairs (only if min a b ≤ degree)
        match findValidCompPairIdx terms degree with
        | some (i, j) =>
          if hi : i < terms.length then
            if hj : j < terms.length then
              if hij : i < j then
                if hlit : terms[j].2 == terms[i].2.negate then
                  if hle : min terms[i].1 terms[j].1 ≤ degree then
                    let pre := terms.take i
                    let mid := (terms.drop (i + 1)).take (j - i - 1)
                    let post := terms.drop (j + 1)
                    go n (pre ++ (terms[i].1 - min terms[i].1 terms[j].1,
                            terms[i].2) :: mid ++
                          (terms[j].1 - min terms[i].1 terms[j].1,
                            terms[i].2.negate) :: post)
                      (degree - min terms[i].1 terms[j].1)
                  else ⟨terms, degree⟩
                else ⟨terms, degree⟩
              else ⟨terms, degree⟩
            else ⟨terms, degree⟩
          else ⟨terms, degree⟩
        | none =>
          -- Priority 3: merge like terms
          match findLikeTermIdx terms with
          | some (i, j) =>
            if hi : i < terms.length then
              if hj : j < terms.length then
                if hij : i < j then
                  if hlit : terms[j].2 == terms[i].2 then
                    let pre := terms.take i
                    let mid := (terms.drop (i + 1)).take (j - i - 1)
                    let post := terms.drop (j + 1)
                    go n (pre ++ (terms[i].1 + terms[j].1,
                            terms[i].2) :: mid ++ post) degree
                  else ⟨terms, degree⟩
                else ⟨terms, degree⟩
              else ⟨terms, degree⟩
            else ⟨terms, degree⟩
          | none => ⟨terms, degree⟩
  -- Fuel: each step reduces terms or zeros; 4 * length + 1 is a safe bound.
  go (normFuel c.terms.length) c.terms c.degree

/-- Add two PB constraints. -/
def addConstrs (c1 c2 : Sat.PB.Constr) : Sat.PB.Constr :=
  ⟨c1.terms ++ c2.terms, c1.degree + c2.degree⟩

/-- Multiply a PB constraint by a positive integer. -/
def mulConstr (c : Sat.PB.Constr) (k : Nat) : Sat.PB.Constr :=
  ⟨c.terms.map fun (a, l) => (k * a, l), k * c.degree⟩

/-- Divide a PB constraint by a positive integer (ceiling). -/
def divConstr (c : Sat.PB.Constr) (k : Nat) : Sat.PB.Constr :=
  ⟨c.terms.map fun (a, l) => (Sat.PB.ceilDiv a k, l), Sat.PB.ceilDiv c.degree k⟩

/-- Saturate a PB constraint: cap coefficients at the degree. -/
def saturateConstr (c : Sat.PB.Constr) : Sat.PB.Constr :=
  ⟨c.terms.map fun (a, l) => (min a c.degree, l), c.degree⟩

/-- Weaken a constraint by a variable (VeriPB `x w`): remove every term of
the variable and subtract the removed coefficients from the degree
(truncated at 0, so a coefficient above the degree gives the trivial
constraint). A variable that does not occur is a no-op. Callers apply this
to the normalized operand, as VeriPB does. -/
def weakenConstr (c : Sat.PB.Constr) (varIdx : Nat) : Sat.PB.Constr :=
  ⟨c.terms.filter fun t => !(t.2.var == varIdx),
   c.degree - Sat.PB.coeffSumR (c.terms.filter fun t => t.2.var == varIdx)⟩

-- RUP via multiply-add-normalize

/-- Find a complementary literal pair between accumulator and hint:
    a literal `l` in acc whose negation `l.negate` appears in hint.
    Returns `(coeffInAcc, coeffInHint, literal in acc)`. -/
def findCompLitPair (acc hint : Sat.PB.Constr) :
    Option (Nat × Nat × Sat.PB.Literal) :=
  acc.terms.findSome? fun (ca, la) =>
    hint.terms.findSome? fun (ch, lh) =>
      if la.var == lh.var && la != lh then some (ca, ch, la)
      else none

-- Solution evaluation for SAT/BOUNDS conclusions

/-- Evaluate a literal under a total assignment (array of Bools). -/
def evalLitBool (asgn : Array Bool) (l : Sat.PB.Literal) : Bool :=
  match l with
  | .pos i => if h : i < asgn.size then asgn[i] else false
  | .neg i => if h : i < asgn.size then !asgn[i] else true

/-- Evaluate a PB constraint under a total assignment. Returns true if satisfied. -/
def evalConstrBool (asgn : Array Bool) (c : Sat.PB.Constr) : Bool :=
  let sum := c.terms.foldl (init := 0) fun acc (a, l) =>
    acc + if evalLitBool asgn l then a else 0
  sum >= c.degree

/-- Evaluate the objective function on an assignment. -/
def evalObjective (asgn : Array Bool) (obj : Sat.PB.Constr) : Nat :=
  obj.terms.foldl (init := 0) fun acc (a, l) =>
    acc + if evalLitBool asgn l then a else 0

-- PB unit propagation for RUP verification

/-- Evaluate a literal under a partial assignment. -/
def evalLitPartial (asgn : Array (Option Bool))
    (l : Sat.PB.Literal) : Option Bool :=
  match l with
  | .pos i => if h : i < asgn.size then asgn[i] else none
  | .neg i => if h : i < asgn.size then asgn[i].map (!·) else none

/-- Result of propagating a single constraint. -/
inductive PropResult where
  | conflict
  | propagated (forced : List (Sat.PB.Literal × Bool))
  | noPropagation
  deriving Repr

/-- Try to propagate a constraint under a partial assignment.
    Returns forced assignments or conflict. -/
def pbPropagate (asgn : Array (Option Bool))
    (c : Sat.PB.Constr) : PropResult := Id.run do
  -- Compute slack = (sum of coeffs for true/unassigned lits) - degree
  let mut totalActive : Nat := 0
  for (a, l) in c.terms do
    match evalLitPartial asgn l with
    | some false => pure () -- falsified, contributes 0
    | _ => totalActive := totalActive + a -- true or unassigned
  if totalActive < c.degree then return .conflict
  let slack := totalActive - c.degree
  -- Find unassigned literals with coefficient > slack
  let mut forced : List (Sat.PB.Literal × Bool) := []
  for (a, l) in c.terms do
    match evalLitPartial asgn l with
    | none =>
      if a > slack then forced := (l, true) :: forced
    | some false => pure ()
    | _ => pure ()
  if forced.isEmpty then .noPropagation
  else .propagated forced.reverse

/-- Run PB unit propagation for a RUP step.
    Returns the index of the conflicting hint (0-based).
    Takes a lookup function to avoid copying the constraint database. -/
def findConflictHint (negConstr : Sat.PB.Constr)
    (hints : List RupHint) (lookupConstr : Nat → Option Sat.PB.Constr)
    (numVars : Nat) : Except String Nat := do
  -- Resolve all hints to constraints upfront (can fail)
  let hintConstrs ← hints.mapM fun h =>
    match h with
    | .negC => .ok negConstr
    | .id n => match lookupConstr n with
      | some c => .ok c
      | none => .error s!"RUP hint {n} not found"
  let hintArr := hintConstrs.toArray
  -- Run propagation loop imperatively
  let result : Option Nat := Id.run do
    let mut asgn : Array (Option Bool) := .replicate numVars none
    let mut conflictIdx : Option Nat := none
    let mut changed := true
    while changed do
      changed := false
      for i in List.range hintArr.size do
        if conflictIdx.isSome then break
        let hintC := hintArr[i]!
        match pbPropagate asgn hintC with
        | .conflict => conflictIdx := some i
        | .propagated forced =>
          changed := true
          for (l, val) in forced do
            if conflictIdx.isSome then break
            let varIdx := l.var
            let actualVal := match l with
              | .pos _ => val
              | .neg _ => !val
            if varIdx < asgn.size then
              match asgn[varIdx]! with
              | some existing =>
                if existing != actualVal then
                  -- Contradictory assignment → conflict at this hint
                  conflictIdx := some i
              | none =>
                asgn := asgn.set! varIdx (some actualVal)
        | .noPropagation => pure ()
    return conflictIdx
  match result with
  | some idx => .ok idx
  | none => .error "RUP: propagation did not reach conflict"

-- Pol RPN evaluator with mixed stack

/-- RPN stack element: either a constraint or a raw integer. -/
inductive StackElem where
  | constr : Sat.PB.Constr → StackElem
  | nat : Nat → StackElem
  deriving Repr

-- Metaprogram layer: Expr-level proof construction

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

/-- ToExpr for Sat.PB.Literal. -/
instance : ToExpr Sat.PB.Literal where
  toTypeExpr := mkConst ``Sat.PB.Literal
  toExpr
    | .pos i => mkApp (mkConst ``Sat.PB.Literal.pos) (mkRawNatLit i)
    | .neg i => mkApp (mkConst ``Sat.PB.Literal.neg) (mkRawNatLit i)

/-- Build a `List Sat.PB.Term` expression from data. -/
def buildTermListExpr (terms : List Sat.PB.Term) : Expr :=
  let termType := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Sat.PB.Literal)
  let nil := mkApp (mkConst ``List.nil [.zero]) termType
  let cons := mkApp (mkConst ``List.cons [.zero]) termType
  terms.foldr (fun (c, l) acc =>
    let pair := mkApp4 (mkConst ``Prod.mk [.zero, .zero])
      (mkConst ``Nat) (mkConst ``Sat.PB.Literal) (mkRawNatLit c) (toExpr l)
    mkApp2 cons pair acc
  ) nil

/-- Build a `PB.Constr` expression from data. -/
def buildConstrExpr (c : Sat.PB.Constr) : Expr :=
  mkApp2 (mkConst ``Sat.PB.Constr.mk) (buildTermListExpr c.terms) (mkRawNatLit c.degree)

/-- A stored constraint with data, Lean expression, and proof. -/
structure StoredConstr where
  constr : Sat.PB.Constr
  expr   : Expr  -- Lean expression of type `PB.Constr`
  proof  : Expr  -- proof of type `PB.PBFmla.proof ctx constr`

/-- Build a PBFmla expression from an array of constraint arrays (balanced tree). -/
def buildConj (constrs : Array Sat.PB.Constr) (start stop : Nat) : Except String Expr :=
  match h : stop - start with
  | 0 => .error "buildConj: empty formula (start == stop)"
  | 1 =>
    match constrs[start]? with
    | some c => .ok <| mkApp (mkConst ``Sat.PB.PBFmla.one) (buildConstrExpr c)
    | none => .error s!"buildConj: index {start} out of bounds"
  | len + 2 =>
    let mid := start + (len + 2) / 2
    do
      let left ← buildConj constrs start mid
      let right ← buildConj constrs mid stop
      .ok <| mkApp2 (mkConst ``Sat.PB.PBFmla.and) left right
termination_by stop - start

/-- Extract proofs for each input constraint via subsumption (like LRAT's buildClauses). -/
def buildClauses (constrs : Array Sat.PB.Constr) (ctx : Expr) (start stop : Nat)
    (f p : Expr) (accum : Nat × Std.HashMap Nat StoredConstr) :
    Except String (Nat × Std.HashMap Nat StoredConstr) :=
  match h : stop - start with
  | 0 => .error "buildClauses: empty range"
  | 1 =>
    match constrs[start]? with
    | some c =>
      let cExpr := f.appArg!
      let proof := mkApp3 (mkConst ``Sat.PB.PBFmla.proof_of_subsumes) ctx cExpr p
      let n := accum.1 + 1
      .ok (n, accum.2.insert n { constr := c, expr := cExpr, proof })
    | none => .error s!"buildClauses: index {start} out of bounds"
  | len + 2 =>
    let mid := start + (len + 2) / 2
    let f₁ := f.appFn!.appArg!
    let f₂ := f.appArg!
    let p₁ := mkApp4 (mkConst ``Sat.PB.PBFmla.subsumes_left) ctx f₁ f₂ p
    let p₂ := mkApp4 (mkConst ``Sat.PB.PBFmla.subsumes_right) ctx f₁ f₂ p
    do
      let accum ← buildClauses constrs ctx start mid f₁ p₁ accum
      buildClauses constrs ctx mid stop f₂ p₂ accum
termination_by stop - start

-- Normalization Expr builder

/-- Build a kernel-checkable proof of `a ≤ b` for concrete Nat literals. -/
def mkNatLeProof (a b : Nat) : Expr :=
  let natLitA := mkRawNatLit a
  let natLitB := mkRawNatLit b
  let leProp := mkApp2
    (mkApp2 (mkConst ``LE.le [.zero]) (mkConst ``Nat) (mkConst ``instLENat))
    natLitA natLitB
  let decInst := mkApp2 (mkConst ``Nat.decLe) natLitA natLitB
  let rflProof := mkApp2
    (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool)
    (mkConst ``Bool.true)
  let decideProp :=
    mkApp2 (mkConst ``Decidable.decide) leProp decInst
  let eqType := mkApp3
    (mkConst ``Eq [.succ .zero]) (mkConst ``Bool)
    decideProp (mkConst ``Bool.true)
  let idProof :=
    mkApp2 (mkConst ``id [.zero]) eqType rflProof
  mkApp3 (mkConst ``of_decide_eq_true) leProp decInst idProof

/-- Build a kernel-checkable proof of `a < b` for concrete Nat literals.
Constructs: `of_decide_eq_true (Nat.decLt a b) (Eq.refl true)` -/
def mkNatLtProof (a b : Nat) : Expr :=
  let natLitA := mkRawNatLit a
  let natLitB := mkRawNatLit b
  let ltProp := mkApp2
    (mkApp2 (mkConst ``LT.lt [.zero])
      (mkConst ``Nat) (mkConst ``instLTNat))
    natLitA natLitB
  let decInst :=
    mkApp2 (mkConst ``Nat.decLt) natLitA natLitB
  let rflProof := mkApp2
    (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool)
    (mkConst ``Bool.true)
  let decideProp :=
    mkApp2 (mkConst ``Decidable.decide) ltProp decInst
  let eqType := mkApp3
    (mkConst ``Eq [.succ .zero]) (mkConst ``Bool)
    decideProp (mkConst ``Bool.true)
  let idProof :=
    mkApp2 (mkConst ``id [.zero]) eqType rflProof
  mkApp3 (mkConst ``of_decide_eq_true) ltProp decInst idProof

/-- Apply one remove-zero step, building the Expr proof using `PB.remove_zero_sat`.
    Proof type: `∀ v, allSat v ctx → newConstr.sat v`
    Built from: `fun v hv => remove_zero_sat v pre post l d (prevProof v hv)` -/
def buildRemoveZero (idx : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (proofExpr : Expr) (ctx : Expr) : List Sat.PB.Term × Nat × Expr × Expr :=
  let pre := terms.take idx
  let post := terms.drop (idx + 1)
  let (_, l) := terms[idx]!
  let preExpr := buildTermListExpr pre
  let postExpr := buildTermListExpr post
  let lExpr := toExpr l
  let dExpr := mkRawNatLit degree
  let vTy := mkConst ``Sat.PB.Valuation
  let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
  let body := mkApp6 (mkConst ``Sat.PB.remove_zero_sat)
    (mkBVar 1) preExpr postExpr lExpr dExpr
    (mkApp2 proofExpr (mkBVar 1) (mkBVar 0))
  let newProof := mkLambda `v .default vTy <| mkLambda `hv .default allSatTy body
  let newTerms := pre ++ post
  let newExpr := buildConstrExpr ⟨newTerms, degree⟩
  (newTerms, degree, newExpr, newProof)

/-- Apply one cancel-pair step, building the Expr proof using `PB.cancel_pair_sat`.
    `idx1 < idx2`, terms[idx1] = (a, l), terms[idx2] = (b, l.negate). -/
def buildCancelPair (idx1 idx2 : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (proofExpr : Expr) (ctx : Expr) : List Sat.PB.Term × Nat × Expr × Expr :=
  let pre := terms.take idx1
  let (a, l) := terms[idx1]!
  let mid := (terms.drop (idx1 + 1)).take (idx2 - idx1 - 1)
  let (b, _) := terms[idx2]!
  let post := terms.drop (idx2 + 1)
  let m := min a b
  let preExpr := buildTermListExpr pre
  let midExpr := buildTermListExpr mid
  let postExpr := buildTermListExpr post
  let lExpr := toExpr l
  let aExpr := mkRawNatLit a
  let bExpr := mkRawNatLit b
  let dExpr := mkRawNatLit degree
  let hleProof := mkNatLeProof m degree
  let vTy := mkConst ``Sat.PB.Valuation
  let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
  let body := mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp
    (mkConst ``Sat.PB.cancel_pair_sat)
    (mkBVar 1)) preExpr) midExpr) postExpr) lExpr) aExpr) bExpr) dExpr) hleProof)
    (mkApp2 proofExpr (mkBVar 1) (mkBVar 0))
  let newProof := mkLambda `v .default vTy <| mkLambda `hv .default allSatTy body
  let newTerms := pre ++ (a - m, l) :: mid ++ (b - m, l.negate) :: post
  let newDegree := degree - m
  let newExpr := buildConstrExpr ⟨newTerms, newDegree⟩
  (newTerms, newDegree, newExpr, newProof)

/-- Apply one merge-terms step, building the Expr proof using `PB.merge_terms_sat`.
    `idx1 < idx2`, terms[idx1] = (a, l), terms[idx2] = (b, l) (same literal). -/
def buildMergeTerms (idx1 idx2 : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (proofExpr : Expr) (ctx : Expr) : List Sat.PB.Term × Nat × Expr × Expr :=
  let pre := terms.take idx1
  let (a, l) := terms[idx1]!
  let mid := (terms.drop (idx1 + 1)).take (idx2 - idx1 - 1)
  let (b, _) := terms[idx2]!
  let post := terms.drop (idx2 + 1)
  let preExpr := buildTermListExpr pre
  let midExpr := buildTermListExpr mid
  let postExpr := buildTermListExpr post
  let lExpr := toExpr l
  let aExpr := mkRawNatLit a
  let bExpr := mkRawNatLit b
  let dExpr := mkRawNatLit degree
  let vTy := mkConst ``Sat.PB.Valuation
  let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
  let body := mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp
    (mkConst ``Sat.PB.merge_terms_sat)
    (mkBVar 1)) preExpr) midExpr) postExpr) lExpr) aExpr) bExpr
  let body := mkApp2 body dExpr (mkApp2 proofExpr (mkBVar 1) (mkBVar 0))
  let newProof := mkLambda `v .default vTy <| mkLambda `hv .default allSatTy body
  let newTerms := pre ++ (a + b, l) :: mid ++ post
  let newExpr := buildConstrExpr ⟨newTerms, degree⟩
  (newTerms, degree, newExpr, newProof)

/-- Normalize a constraint by iteratively removing zeros and canceling
    complementary pairs, building kernel-verified proof at each step. -/
def buildNormalization (rawConstr : Sat.PB.Constr) (rawExpr : Expr)
    (rawProof : Expr) (ctx : Expr) :
    Sat.PB.Constr × Expr × Expr :=
  let rec go (fuel : Nat) (terms : List Sat.PB.Term) (degree : Nat)
      (constrExpr proofExpr : Expr) : Sat.PB.Constr × Expr × Expr :=
    match fuel with
    | 0 => (⟨terms, degree⟩, constrExpr, proofExpr)
    | n + 1 =>
      -- Priority 1: remove zero-coefficient terms
      match findZeroIdx terms with
      | some idx =>
        let (t', d', e', p') := buildRemoveZero idx terms degree proofExpr ctx
        go n t' d' e' p'
      | none =>
        -- Priority 2: cancel complementary pairs (only if min a b ≤ degree)
        match findValidCompPairIdx terms degree with
        | some (i, j) =>
          let (t', d', e', p') := buildCancelPair i j terms degree proofExpr ctx
          go n t' d' e' p'
        | none =>
          -- Priority 3: merge like terms
          match findLikeTermIdx terms with
          | some (i, j) =>
            let (t', d', e', p') := buildMergeTerms i j terms degree proofExpr ctx
            go n t' d' e' p'
          | none =>
            -- Fully normalized
            (⟨terms, degree⟩, constrExpr, proofExpr)
  -- Fuel bound: each cancel-pair step may produce a zero that needs a second step to remove
  -- (2 fuel per pair), plus initial zeros and like-term merges. 4 * length + 1 is a safe bound.
  go (normFuel rawConstr.terms.length) rawConstr.terms rawConstr.degree rawExpr rawProof

-- Direct normalization (for RUP: produces c.sat v proofs, not wrapped)

/-- Expr-level weakening by a variable: remove the terms of `varIdx` one at
a time, each step justified by `Sat.PB.weaken_term_sat`. Returns the final
constraint and its proof `fun v hv => ...`. `fuel` bounds the number of
removals (the number of terms suffices). -/
def buildWeakenVar (varIdx : Nat) (ctx : Expr) : Nat → Sat.PB.Constr → Expr →
    Sat.PB.Constr × Expr
  | 0, cur, curProof => (cur, curProof)
  | fuel + 1, cur, curProof =>
    match cur.terms.findIdx? fun (_, l) => l.var == varIdx with
    | none => (cur, curProof)
    | some idx =>
      let pre := cur.terms.take idx
      let (a, l) := cur.terms[idx]!
      let post := cur.terms.drop (idx + 1)
      let vTy := mkConst ``Sat.PB.Valuation
      let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
      -- weaken_term_sat v pre post a l d (curProof v hv)
      let body := mkApp7 (mkConst ``Sat.PB.weaken_term_sat)
        (mkBVar 1) (buildTermListExpr pre) (buildTermListExpr post)
        (mkRawNatLit a) (toExpr l) (mkRawNatLit cur.degree)
        (mkApp2 curProof (mkBVar 1) (mkBVar 0))
      let proof := mkLambda `v .default vTy <|
        mkLambda `hv .default allSatTy body
      buildWeakenVar varIdx ctx fuel ⟨pre ++ post, cur.degree - a⟩ proof

/-- Remove a zero-coefficient term, producing a direct `c.sat v` proof.
    `vExpr` is the expression for the valuation variable `v`. -/
def buildRemoveZeroDirect (idx : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (proofExpr : Expr) (vExpr : Expr) : List Sat.PB.Term × Nat × Expr × Expr :=
  let pre := terms.take idx
  let post := terms.drop (idx + 1)
  let (_, l) := terms[idx]!
  let preExpr := buildTermListExpr pre
  let postExpr := buildTermListExpr post
  let lExpr := toExpr l
  let dExpr := mkRawNatLit degree
  let body := mkApp6 (mkConst ``Sat.PB.remove_zero_sat) vExpr preExpr postExpr lExpr dExpr proofExpr
  let newTerms := pre ++ post
  let newExpr := buildConstrExpr ⟨newTerms, degree⟩
  (newTerms, degree, newExpr, body)

/-- Cancel a complementary pair, producing a direct `c.sat v` proof. -/
def buildCancelPairDirect (idx1 idx2 : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (proofExpr : Expr) (vExpr : Expr) : List Sat.PB.Term × Nat × Expr × Expr :=
  let pre := terms.take idx1
  let (a, l) := terms[idx1]!
  let mid := (terms.drop (idx1 + 1)).take (idx2 - idx1 - 1)
  let (b, _) := terms[idx2]!
  let post := terms.drop (idx2 + 1)
  let m := min a b
  let preExpr := buildTermListExpr pre
  let midExpr := buildTermListExpr mid
  let postExpr := buildTermListExpr post
  let lExpr := toExpr l
  let aExpr := mkRawNatLit a
  let bExpr := mkRawNatLit b
  let dExpr := mkRawNatLit degree
  let hleProof := mkNatLeProof m degree
  let body := mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp
    (mkConst ``Sat.PB.cancel_pair_sat)
    vExpr) preExpr) midExpr) postExpr) lExpr) aExpr) bExpr) dExpr) hleProof) proofExpr
  let newTerms := pre ++ (a - m, l) :: mid ++ (b - m, l.negate) :: post
  let newDegree := degree - m
  let newExpr := buildConstrExpr ⟨newTerms, newDegree⟩
  (newTerms, newDegree, newExpr, body)

/-- Merge like terms, producing a direct `c.sat v` proof. -/
def buildMergeTermsDirect (idx1 idx2 : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (proofExpr : Expr) (vExpr : Expr) : List Sat.PB.Term × Nat × Expr × Expr :=
  let pre := terms.take idx1
  let (a, l) := terms[idx1]!
  let mid := (terms.drop (idx1 + 1)).take (idx2 - idx1 - 1)
  let (b, _) := terms[idx2]!
  let post := terms.drop (idx2 + 1)
  let preExpr := buildTermListExpr pre
  let midExpr := buildTermListExpr mid
  let postExpr := buildTermListExpr post
  let lExpr := toExpr l
  let aExpr := mkRawNatLit a
  let bExpr := mkRawNatLit b
  let dExpr := mkRawNatLit degree
  let body := mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp
    (mkConst ``Sat.PB.merge_terms_sat)
    vExpr) preExpr) midExpr) postExpr) lExpr) aExpr) bExpr
  let body := mkApp2 body dExpr proofExpr
  let newTerms := pre ++ (a + b, l) :: mid ++ post
  let newExpr := buildConstrExpr ⟨newTerms, degree⟩
  (newTerms, degree, newExpr, body)

/-- Normalize a constraint with direct `c.sat v` proofs (for RUP). -/
def buildNormDirect (rawConstr : Sat.PB.Constr) (rawExpr : Expr)
    (rawProof : Expr) (vExpr : Expr) :
    Sat.PB.Constr × Expr × Expr :=
  let rec go (fuel : Nat) (terms : List Sat.PB.Term) (degree : Nat)
      (constrExpr proofExpr : Expr) : Sat.PB.Constr × Expr × Expr :=
    match fuel with
    | 0 => (⟨terms, degree⟩, constrExpr, proofExpr)
    | n + 1 =>
      match findZeroIdx terms with
      | some idx =>
        let (t', d', e', p') := buildRemoveZeroDirect idx terms degree proofExpr vExpr
        go n t' d' e' p'
      | none =>
        match findValidCompPairIdx terms degree with
        | some (i, j) =>
          let (t', d', e', p') := buildCancelPairDirect i j terms degree proofExpr vExpr
          go n t' d' e' p'
        | none =>
          match findLikeTermIdx terms with
          | some (i, j) =>
            let (t', d', e', p') := buildMergeTermsDirect i j terms degree proofExpr vExpr
            go n t' d' e' p'
          | none =>
            (⟨terms, degree⟩, constrExpr, proofExpr)
  -- Fuel bound: each cancel-pair step may produce a zero that needs a second step to remove
  -- (2 fuel per pair), plus initial zeros and like-term merges. 4 * length + 1 is a safe bound.
  go (normFuel rawConstr.terms.length) rawConstr.terms rawConstr.degree rawExpr rawProof

-- Pol RPN proof builder

/-- RPN stack element for the metaprogram: constraint data + expr + proof. -/
inductive MetaStackElem where
  | constr : StoredConstr → MetaStackElem
  | nat : Nat → MetaStackElem

/-- Execute pol RPN and build proof terms.
    Each stored proof has type `PBFmla.proof ctx c`. -/
def buildPolProof (ops : List PolOp) (db : Std.HashMap Nat StoredConstr)
    (ctx : Expr) :
    Except String StoredConstr := do
  let execOne (stack : List MetaStackElem) (op : PolOp) :
      Except String (List MetaStackElem) :=
    match op with
    | .pushId id =>
      match db[id]? with
      | some sc => .ok (.constr sc :: stack)
      | none => .error s!"pol: constraint ID {id} not in database"
    | .pushNat n => .ok (.nat n :: stack)
    | .pushLitAxiom lit => do
      let pbLit ← opbLitToPB lit
      let c : Sat.PB.Constr := ⟨[(1, pbLit)], 0⟩
      let cExpr := buildConstrExpr c
      -- Proof: lit_axiom is unconditionally satisfied
      -- PBFmla.proof ctx c = ∀ v, allSat v → c.sat v
      -- = fun v _ => lit_axiom_pos/neg i v
      let vTy := mkConst ``Sat.PB.Valuation
      let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
      let axiomProof := match pbLit with
        | .pos i => mkApp2 (mkConst ``Sat.PB.lit_axiom_pos) (mkRawNatLit i) (mkBVar 1)
        | .neg i => mkApp2 (mkConst ``Sat.PB.lit_axiom_neg) (mkRawNatLit i) (mkBVar 1)
      let proof := mkLambda `v .default vTy <|
        mkLambda `_ .default allSatTy axiomProof
      .ok (.constr ⟨c, cExpr, proof⟩ :: stack)
    | .add =>
      match stack with
      | .constr sc2 :: .constr sc1 :: rest =>
        let newConstr := addConstrs sc1.constr sc2.constr
        let newExpr := buildConstrExpr newConstr
        -- Proof: fun v hv => add_sat c1 c2 v (sc1.proof v hv) (sc2.proof v hv)
        let vTy := mkConst ``Sat.PB.Valuation
        let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
        let p1 := mkApp2 sc1.proof (mkBVar 1) (mkBVar 0)
        let p2 := mkApp2 sc2.proof (mkBVar 1) (mkBVar 0)
        let addApp := mkApp5 (mkConst ``Sat.PB.add_sat)
          sc1.expr sc2.expr (mkBVar 1) p1 p2
        let proof := mkLambda `v .default vTy <|
          mkLambda `hv .default allSatTy addApp
        .ok (.constr ⟨newConstr, newExpr, proof⟩ :: rest)
      | _ => .error "pol +: need two constraints on stack"
    | .mul =>
      match stack with
      | .nat k :: .constr sc :: rest =>
        -- k=0 is valid: zeroes out the constraint (useful for masking terms)
        let newConstr := mulConstr sc.constr k
        let newExpr := buildConstrExpr newConstr
        -- Proof: fun v hv => mul_sat c k v (sc.proof v hv)
        let vTy := mkConst ``Sat.PB.Valuation
        let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
        let p := mkApp2 sc.proof (mkBVar 1) (mkBVar 0)
        let mulApp := mkApp4 (mkConst ``Sat.PB.mul_sat) sc.expr (mkRawNatLit k) (mkBVar 1) p
        let proof := mkLambda `v .default vTy <|
          mkLambda `hv .default allSatTy mulApp
        .ok (.constr ⟨newConstr, newExpr, proof⟩ :: rest)
      | _ => .error "pol *: need integer on top of constraint on stack"
    | .div =>
      match stack with
      | .nat k :: .constr sc :: rest =>
        if k == 0 then .error "pol d: divisor must be positive"
        else
          -- VeriPB normalizes before division (cancel complementary pairs first)
          let (normC, normE, normP) := buildNormalization sc.constr sc.expr sc.proof ctx
          let newConstr := divConstr normC k
          let newExpr := buildConstrExpr newConstr
          -- Proof: fun v hv => div_sat normC k hk v (normP v hv)
          let vTy := mkConst ``Sat.PB.Valuation
          let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
          let p := mkApp2 normP (mkBVar 1) (mkBVar 0)
          let hkProof := mkNatLtProof 0 k
          let divApp := mkApp5 (mkConst ``Sat.PB.div_sat)
            normE (mkRawNatLit k) hkProof (mkBVar 1) p
          let proof := mkLambda `v .default vTy <|
            mkLambda `hv .default allSatTy divApp
          .ok (.constr ⟨newConstr, newExpr, proof⟩ :: rest)
      | _ => .error "pol d: need integer on top of constraint on stack"
    | .saturate =>
      match stack with
      | .constr sc :: rest =>
        -- VeriPB normalizes before saturation (cancel complementary pairs first)
        let (normC, normE, normP) := buildNormalization sc.constr sc.expr sc.proof ctx
        let newConstr := saturateConstr normC
        let newExpr := buildConstrExpr newConstr
        -- Proof: fun v hv => saturate_sat normC v (normP v hv)
        let vTy := mkConst ``Sat.PB.Valuation
        let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
        let p := mkApp2 normP (mkBVar 1) (mkBVar 0)
        let satApp := mkApp3 (mkConst ``Sat.PB.saturate_sat) normE (mkBVar 1) p
        let proof := mkLambda `v .default vTy <|
          mkLambda `hv .default allSatTy satApp
        .ok (.constr ⟨newConstr, newExpr, proof⟩ :: rest)
      | _ => .error "pol s: need constraint on stack"
    | .weaken varName =>
      match stack with
      | .constr sc :: rest => do
        let varIdx ← if varName.startsWith "x" then
          match (varName.drop 1).toString.toNat? with
          | some n => if n > 0 then pure (n - 1) else .error "variable index must be > 0"
          | none => .error s!"invalid variable in weaken: {varName}"
        else
          .error s!"expected variable name starting with 'x', got: {varName}"
        -- VeriPB weakens the normalized constraint and removes every term of
        -- the variable (absent variable: no-op; coefficient above the degree:
        -- trivial constraint). Same result as `weakenConstr (normalizeConstr c)`.
        let (normC, _normE, normP) := buildNormalization sc.constr sc.expr sc.proof ctx
        let (newConstr, proof) := buildWeakenVar varIdx ctx normC.terms.length normC normP
        .ok (.constr ⟨newConstr, buildConstrExpr newConstr, proof⟩ :: rest)
      | _ => .error "pol w: need constraint on stack"
    | .lowerRhs => .error "unsupported in veripb_proof: pol operation '-'"
    | .divVar => .error "unsupported in veripb_proof: pol operation 'c'"
    | .mir => .error "unsupported in veripb_proof: pol operation 'n'"
    | .mirVar => .error "unsupported in veripb_proof: pol operation 'm'"
  let finalStack ← ops.foldlM (init := ([] : List MetaStackElem)) execOne
  match finalStack with
  | [.constr sc] =>
    -- Normalize at the end of the pol step (not after each intermediate operation)
    let (normC, normE, normP) := buildNormalization sc.constr sc.expr sc.proof ctx
    .ok ⟨normC, normE, normP⟩
  | [.nat _] => .error "pol: stack ends with integer, not constraint"
  | [] => .error "pol: empty stack at end"
  | _ => .error s!"pol: stack has {finalStack.length} elements at end, expected 1"

-- RUP proof builder

/-- Build a RUP proof using conflict-hint-first approach.
    Uses PB unit propagation to find the conflicting hint, starts the
    accumulator from it, then adds remaining hints via multiply-add-normalize.
    Proof structure:
    ```
    fun v hv => Classical.byContradiction fun hn =>
      let acc := conflict_hint_sat  -- start from conflict hint
      let acc := add_sat + normalize (acc, other hints) ...
      absurd accSat (contra_unsat acc v hc)
    ```
    Inside byContradiction body: BVar 0 = hn, BVar 1 = hv, BVar 2 = v -/
def buildRupProof (targetOPB : OPBConstr) (hints : List RupHint)
    (db : Std.HashMap Nat StoredConstr) (ctx : Expr) (numVars : Nat) :
    Except String StoredConstr := do
  -- Convert target to PB
  let targetConstr ← opbConstrToPB targetOPB
  -- Compute the negation at data level
  let negConstr := targetConstr.negate
  -- Verify precondition: degree ≤ coeffSum
  let cs := targetConstr.coeffSum
  if targetConstr.degree > cs then
    throw s!"RUP: target degree {targetConstr.degree} > coeffSum {cs}"
  if hints.isEmpty then
    throw "RUP: no hints provided"
  -- Find the conflicting hint via PB unit propagation
  let lookupConstr (n : Nat) : Option Sat.PB.Constr :=
    db[n]?.map (·.constr)
  let conflictIdx ← findConflictHint negConstr hints lookupConstr numVars
  -- We'll build the proof body inside byContradiction.
  -- Under `fun v hv => Classical.byContradiction fun hn => ...`:
  --   BVar 0 = hn : ¬ targetConstr.sat v
  --   BVar 1 = hv : allSat v ctx
  --   BVar 2 = v  : Valuation
  let vExpr := mkBVar 2       -- v
  let hvExpr := mkBVar 1      -- hv
  let hnExpr := mkBVar 0      -- hn
  -- Build negation proof: negate_sat_of_not_sat C v hd hn
  let targetExpr := buildConstrExpr targetConstr
  let hdProof := mkNatLeProof targetConstr.degree cs
  let negProof := mkApp4 (mkConst ``Sat.PB.negate_sat_of_not_sat)
    targetExpr vExpr hdProof hnExpr
  let negExpr := buildConstrExpr negConstr
  -- Helper to get hint data + expr + proof
  let getHintProof (h : RupHint) : Except String (Sat.PB.Constr × Expr × Expr) :=
    match h with
    | .negC => .ok (negConstr, negExpr, negProof)
    | .id n =>
      match db[n]? with
      | some sc =>
        let satProof := mkApp2 sc.proof vExpr hvExpr
        .ok (sc.constr, sc.expr, satProof)
      | none => .error s!"RUP: hint constraint {n} not in database"
  -- Start accumulator from the conflict hint
  let (initC, initE, initP) ← getHintProof hints[conflictIdx]!
  let initAcc := buildNormDirect initC initE initP vExpr
  -- Process all other hints (skipping conflict hint) via multiply-add-normalize
  let hintsArr := hints.toArray
  let processHint (acc : Sat.PB.Constr × Expr × Expr)
      (idx : Nat) : Except String (Sat.PB.Constr × Expr × Expr) := do
    let (accC, accE, accP) := acc
    if accC.isContra then return acc
    let (hintC, hintE, hintP) ← getHintProof hintsArr[idx]!
    match findCompLitPair accC hintC with
    | some (ca, ch, _) =>
      -- Multiply acc by ch, hint by ca for full cancellation
      let (mAccC, mAccE, mAccP) := if ch == 1 then (accC, accE, accP)
        else
          let mc := mulConstr accC ch
          let me := buildConstrExpr mc
          let mp := mkApp4 (mkConst ``Sat.PB.mul_sat)
            accE (mkRawNatLit ch) vExpr accP
          (mc, me, mp)
      let (mHintC, mHintE, mHintP) := if ca == 1 then (hintC, hintE, hintP)
        else
          let mc := mulConstr hintC ca
          let me := buildConstrExpr mc
          let mp := mkApp4 (mkConst ``Sat.PB.mul_sat)
            hintE (mkRawNatLit ca) vExpr hintP
          (mc, me, mp)
      let addedC := addConstrs mAccC mHintC
      let addedE := buildConstrExpr addedC
      let addedP := mkApp5 (mkConst ``Sat.PB.add_sat)
        mAccE mHintE vExpr mAccP mHintP
      .ok (buildNormDirect addedC addedE addedP vExpr)
    | none =>
      let addedC := addConstrs accC hintC
      let addedE := buildConstrExpr addedC
      let addedP := mkApp5 (mkConst ``Sat.PB.add_sat)
        accE hintE vExpr accP hintP
      .ok (buildNormDirect addedC addedE addedP vExpr)
  -- Build list of hint indices to process (all except conflictIdx)
  let otherIndices := (List.range hints.length).filter (· != conflictIdx)
  let (accC, accE, accP) ← otherIndices.foldlM processHint initAcc
  if !accC.isContra then
    throw s!"RUP: not contradictory after processing hints \
      (coeffSum={accC.coeffSum}, degree={accC.degree}, \
      terms={accC.terms.length})"
  -- Build: absurd accP (contra_unsat accC v hc)
  let hcProof := mkNatLtProof accC.coeffSum accC.degree
  let contraApp := mkApp3 (mkConst ``Sat.PB.contra_unsat) accE vExpr hcProof
  let satType := mkApp2 (mkConst ``Sat.PB.Constr.sat) accE vExpr
  let absurdApp := mkApp4 (mkConst ``absurd [.zero])
    satType (mkConst ``False) accP contraApp
  -- Build: fun v hv => Classical.byContradiction fun hn => absurdApp
  let vExprOuter := mkBVar 1
  let satTargetType := mkApp2 (mkConst ``Sat.PB.Constr.sat)
    targetExpr vExprOuter
  let hnType := mkApp (mkConst ``Not) satTargetType
  let byContraBody := mkLambda `hn .default hnType absurdApp
  let byContraProof := mkApp2 (mkConst ``Classical.byContradiction [])
    satTargetType byContraBody
  -- Normalize targetConstr to get the final result
  let (finalC, finalE, finalP) := buildNormDirect targetConstr targetExpr
    byContraProof vExprOuter
  -- Wrap in fun v hv =>
  let vTy := mkConst ``Sat.PB.Valuation
  let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
  let wrappedProof := mkLambda `v .default vTy <|
    mkLambda `hv .default allSatTy finalP
  .ok ⟨finalC, finalE, wrappedProof⟩

-- Main proof builder

/-- Execute inner proof steps, returning the updated DB and next ID.
    Used by both top-level `buildProof` and `buildPbcProof` for subproofs.
    Does NOT handle conclusion steps — caller must handle those. -/
partial def execInnerSteps (db : Std.HashMap Nat StoredConstr)
    (nextId : Nat) (steps : Array ProofStep) (ctx : Expr) (numVars : Nat) :
    Except String (Std.HashMap Nat StoredConstr × Nat) := do
  let mut db := db
  let mut nextId := nextId
  for step in steps do
    match step with
    | .formulaSize _ => pure ()
    | .pol ops =>
      let sc ← match buildPolProof ops db ctx with
        | .ok sc => .ok sc
        | .error e => .error s!"step {nextId}: {e}"
      db := db.insert nextId sc
      nextId := nextId + 1
    | .rup constr hints =>
      let sc ← match buildRupProof constr hints db ctx numVars with
        | .ok sc => .ok sc
        | .error e => .error s!"step {nextId}: {e}"
      db := db.insert nextId sc
      nextId := nextId + 1
    | .pbc constrOPB innerSteps resultId =>
      let (sc, newNextId) ← buildPbcStep constrOPB innerSteps resultId
        db ctx nextId numVars
      db := db.insert newNextId sc
      nextId := newNextId + 1
    | .red _ _ _ =>
      throw "red steps in Expr-building mode not yet supported; use reflection checker"
    | .deld ids =>
      for id in ids do db := db.erase id
    | .delc ids =>
      for id in ids do db := db.erase id
    | .output => pure ()
    | .conclusion _ => pure ()  -- handled by caller
    -- `sol` adds no constraint and its solution does not affect an
    -- unsatisfiability proof, so it is skipped (unchecked)
    | .sol _ _ => pure ()
    -- `soli` adds the objective-improving constraint under a new ID, which
    -- this path cannot build; skipping it would shift every later ID
    | .soli _ _ => throw "unsupported in veripb_proof: soli"
    | .conclusionSat _ => pure ()  -- conclusions handled by caller
    | .conclusionBounds _ _ _ _ => pure ()  -- conclusions handled by caller
    | .ia .. => throw "unsupported in veripb_proof: ia"
    | .delcChecked .. => throw "unsupported in veripb_proof: checked delc"
    | .core .. | .coreRange .. => throw "unsupported in veripb_proof: core"
    | .strengtheningToCore _ =>
      throw "unsupported in veripb_proof: strengthening_to_core"
    | .dom .. | .strengthening .. => throw "unsupported in veripb_proof: dom/red"
    | .proofgoal .. | .scope .. =>
      throw "unsupported in veripb_proof: proofgoal/scope outside red"
    | .defOrder _ | .loadOrder .. =>
      throw "unsupported in veripb_proof: def_order/load_order"
    | .obji _ | .eobj _ | .obju .. =>
      throw "unsupported in veripb_proof: obji/eobj/obju"
    | .outputClaim .. => throw "unsupported in veripb_proof: output claim"
    | .conclusionNone => throw "unsupported in veripb_proof: conclusion NONE"
  return (db, nextId)
where
  /-- Build a pbc subproof step. Returns StoredConstr for the derived
      constraint and the next ID to use after the subproof.
      Strategy: create extended context, lift DB, run inner steps,
      extract contradiction, apply pbc_sound. -/
  buildPbcStep (constrOPB : OPBConstr) (innerSteps : Array ProofStep)
      (resultId : Nat) (db : Std.HashMap Nat StoredConstr) (ctx : Expr)
      (nextIdStart : Nat) (numVars : Nat) :
      Except String (StoredConstr × Nat) := do
    -- Reject conclusion/output steps inside subproofs
    if innerSteps.any (fun s => match s with
        | .conclusion _ | .output => true | _ => false) then
      throw "pbc subproof contains 'conclusion' or 'output' step"
    -- Convert target to PB
    let targetConstr ← opbConstrToPB constrOPB
    let cs := targetConstr.coeffSum
    if targetConstr.degree > cs then
      throw s!"pbc: target degree {targetConstr.degree} > coeffSum {cs}"
    let negConstr := targetConstr.negate
    let targetExpr := buildConstrExpr targetConstr
    let negExpr := buildConstrExpr negConstr
    -- Build ctx_ext = PBFmla.and ctx (PBFmla.one negConstr)
    let oneNeg := mkApp (mkConst ``Sat.PB.PBFmla.one) negExpr
    let ctxExt := mkApp2 (mkConst ``Sat.PB.PBFmla.and) ctx oneNeg
    -- Lift existing DB entries from ctx to ctx_ext
    -- For each sc with proof : ∀ v, allSat v ctx → c.sat v
    -- Build: fun v hv_ext => sc.proof v (allSat_and_left hv_ext)
    let vTy := mkConst ``Sat.PB.Valuation
    let allSatExtTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctxExt
    let extractLeft := mkApp4 (mkConst ``Sat.PB.allSat_and_left)
      (mkBVar 1) ctx oneNeg (mkBVar 0)
    let mut subDb : Std.HashMap Nat StoredConstr := {}
    for (id, sc) in db.toList do
      let liftedBody := mkApp2 sc.proof (mkBVar 1) extractLeft
      let liftedProof := mkLambda `v .default vTy <|
        mkLambda `hv .default allSatExtTy liftedBody
      subDb := subDb.insert id { sc with proof := liftedProof }
    -- Add negated constraint via subsumption
    let selfSub := mkApp (mkConst ``Sat.PB.PBFmla.subsumes_self) ctxExt
    let subRight := mkApp4
      (mkConst ``Sat.PB.PBFmla.subsumes_right) ctxExt ctx oneNeg selfSub
    let negProof := mkApp3
      (mkConst ``Sat.PB.PBFmla.proof_of_subsumes) ctxExt negExpr subRight
    let negId := nextIdStart
    subDb := subDb.insert negId
      { constr := negConstr, expr := negExpr, proof := negProof }
    -- Run inner steps in ctx_ext
    let (finalDb, finalNextId) ← execInnerSteps subDb (negId + 1)
      innerSteps ctxExt numVars
    -- Look up the qed result — must be contradictory
    match finalDb[resultId]? with
    | none => throw s!"pbc qed: constraint {resultId} not in database"
    | some sc =>
      if !sc.constr.isContra then
        throw s!"pbc qed: constraint {resultId} is not contradictory \
          (coeffSum={sc.constr.coeffSum}, degree={sc.constr.degree})"
      -- Build the inner contradiction: ∀ v, allSat v ctx_ext → False
      let allSatExtTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctxExt
      let satProof := mkApp2 sc.proof (mkBVar 1) (mkBVar 0)
      let hcProof := mkNatLtProof sc.constr.coeffSum sc.constr.degree
      let contraApp := mkApp3
        (mkConst ``Sat.PB.contra_unsat) sc.expr (mkBVar 1) hcProof
      let satType := mkApp2 (mkConst ``Sat.PB.Constr.sat) sc.expr (mkBVar 1)
      let absurdApp := mkApp4 (mkConst ``absurd [.zero])
        satType (mkConst ``False) satProof contraApp
      let innerContra := mkLambda `v .default vTy <|
        mkLambda `hv .default allSatExtTy absurdApp
      -- innerContra : ∀ v, allSat v ctx_ext → False
      -- Transform to: ∀ v, allSat v ctx → C.negate.sat v → False
      -- = fun v hv hneg => innerContra v (allSat_and_intro hv (allSat_one hneg))
      let allSatCtxTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
      let negSatTy := mkApp2 (mkConst ``Sat.PB.Constr.sat) negExpr (mkBVar 1)
      -- Under fun v hv hneg: BVar 0 = hneg, BVar 1 = hv, BVar 2 = v
      let oneProof := mkApp3 (mkConst ``Sat.PB.allSat_one)
        (mkBVar 2) negExpr (mkBVar 0)
      let introProof := mkApp5 (mkConst ``Sat.PB.allSat_and_intro)
        (mkBVar 2) ctx oneNeg (mkBVar 1) oneProof
      let contraBody := mkApp2 innerContra (mkBVar 2) introProof
      let hBody := mkLambda `v .default vTy <|
        mkLambda `hv .default allSatCtxTy <|
          mkLambda `hneg .default negSatTy contraBody
      -- hBody : ∀ v, allSat v ctx → C.negate.sat v → False
      -- Apply pbc_sound: pbc_sound ctx C hd hBody
      let hdProof := mkNatLeProof targetConstr.degree cs
      let pbcProof := mkApp4 (mkConst ``Sat.PB.pbc_sound)
        ctx targetExpr hdProof hBody
      -- Normalize the target constraint
      let (normC, normE, normP) :=
        buildNormalization targetConstr targetExpr pbcProof ctx
      .ok (⟨normC, normE, normP⟩, finalNextId)

/-- Build the main proof of unsatisfiability.
    Returns a proof of type `∀ v, allSat v ctx → False`. -/
partial def buildProof (constrs : Array Sat.PB.Constr) (ctx ctx' : Expr)
    (steps : Array ProofStep) (numVars : Nat) : Except String Expr := do
  let p := mkApp (mkConst ``Sat.PB.PBFmla.subsumes_self) ctx
  let initDb := (← buildClauses constrs ctx 0 constrs.size ctx' p default).2
  let initNextId := constrs.size + 1
  let (db, _) ← execInnerSteps initDb initNextId steps ctx numVars
  -- Find the conclusion step
  for step in steps do
    match step with
    | .conclusion id =>
      match db[id]? with
      | some sc =>
        if sc.constr.isContra then
          let vTy := mkConst ``Sat.PB.Valuation
          let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
          let satProof := mkApp2 sc.proof (mkBVar 1) (mkBVar 0)
          let hcProof := mkNatLtProof sc.constr.coeffSum sc.constr.degree
          let contraApp := mkApp3 (mkConst ``Sat.PB.contra_unsat) sc.expr (mkBVar 1) hcProof
          let satType := mkApp2 (mkConst ``Sat.PB.Constr.sat) sc.expr (mkBVar 1)
          let absurdApp := mkApp4 (mkConst ``absurd [.zero])
            satType (mkConst ``False) satProof contraApp
          let finalProof := mkLambda `v .default vTy <|
            mkLambda `hv .default allSatTy absurdApp
          return finalProof
        else
          throw s!"conclusion constraint {id} is not contradictory"
      | none => throw s!"conclusion constraint {id} not in database"
    | _ => pure ()
  throw "no conclusion step found"

-- Propositional reification (Bool-to-Prop bridge)

/-- Check if an expression is `List.nil`. -/
private def isNilExpr (e : Expr) : Bool :=
  e.isAppOf ``List.nil

/-- Build the reified propositional theorem from the PB unsatisfiability proof.
    Transforms `∀ v : Valuation, allSat v ctx → False` into
    `∀ (a₁ ... aₙ : Prop), (reified negation of formula)`.

    Works under `2*nvars + 1` quantifiers:
    `a₁ .. aₙ : Prop, pv : Nat → Prop, h₁ : pv 0 ↔ a₁, ..., hₙ : pv (n-1) ↔ aₙ`

    Mirrors LRAT's `buildReify` from `FromLRAT.lean`. -/
partial def buildReify (ctx ctx' proof : Expr) (nvars : Nat) : Except String (Expr × Expr) := do
  let (e, pr) ← reifyFmla ctx'
  -- Build: fun (pv : Nat → Prop) (h₁ : pv 0 ↔ a₁) ... (hₙ : pv (n-1) ↔ aₙ) => pr
  let mut pr := pr
  for i in [0:nvars] do
    let j := nvars - i - 1
    -- hⱼ : pv j ↔ aⱼ
    -- pv is at BVar j (relative to current depth), aⱼ is at BVar nvars (further out)
    let ty := mkApp2 (mkConst ``Iff) (mkApp (mkBVar j) (mkRawNatLit j)) (mkBVar nvars)
    pr := mkLambda `h .default ty pr
  -- pv : Nat → Prop
  let pvType := mkForall `_ .default (mkConst ``Nat) (mkSort .zero)
  pr := mkLambda `v .default pvType pr
  -- Lower `e` out of the pv + h₁..hₙ binders
  let mut e := e.lowerLooseBVars (nvars + 1) (nvars + 1)
  -- Build ps = [a₁, ..., aₙ] : List Prop
  let cons := mkApp (mkConst ``List.cons [.zero]) (mkSort .zero)
  let nil := mkApp (mkConst ``List.nil [.zero]) (mkSort .zero)
  let rec mkPS depth e
    | 0 => e
    | n + 1 => mkPS (depth + 1) (mkApp2 cons (mkBVar depth) e) n
  pr := mkApp5 (mkConst ``Sat.PB.PBFmla.refuteProp) e (mkPS 0 nil nvars) ctx proof pr
  -- Introduce ∀ a₁ ... aₙ : Prop
  for _ in [0:nvars] do
    e := mkForall `a .default (mkSort .zero) e
    pr := mkLambda `a .default (mkSort .zero) pr
  pure (e, pr)
where
  /-- The `pv` variable under the `a₁ ... aₙ, pv, h₁ ... hₙ` context -/
  pv := mkBVar nvars
  /-- Reify a PBFmla expression into a propositional expression. -/
  reifyFmla (f : Expr) : Except String (Expr × Expr) :=
    match f.getAppFn.constName? with
    | some ``Sat.PB.PBFmla.and =>
      let f₁ := f.appFn!.appArg!
      let f₂ := f.appArg!
      do
        let (e₁, h₁) ← reifyFmla f₁
        let (e₂, h₂) ← reifyFmla f₂
        .ok (mkApp2 (mkConst ``Or) e₁ e₂,
         mkApp7 (mkConst ``Sat.PB.PBFmla.Reify_or) pv f₁ e₁ f₂ e₂ h₁ h₂)
    | some ``Sat.PB.PBFmla.one =>
      let c := f.appArg!
      do
        let (e, h) ← reifyConstr c
        .ok (e, mkApp4 (mkConst ``Sat.PB.PBFmla.Reify_one) pv c e h)
    | some name => .error s!"buildReify.reifyFmla: unexpected formula head '{name}'"
    | none => .error "buildReify.reifyFmla: expression has no constant head"
  /-- Reify a constraint expression (walks the term list for CNF constraints). -/
  reifyConstr (c : Expr) : Except String (Expr × Expr) :=
    -- c is `Constr.mk terms degree`
    let terms := c.appFn!.appArg!
    if isNilExpr terms then
      .ok (mkConst ``True, mkApp (mkConst ``Sat.PB.Constr.Reify_cnf_zero) pv)
    else reifyConstr1 terms
  /-- Reify a nonempty constraint term list. -/
  reifyConstr1 (terms : Expr) : Except String (Expr × Expr) :=
    -- terms is `List.cons (Prod.mk coeff lit) rest`
    let pair := terms.appFn!.appArg!  -- (coeff, lit) : Prod Nat Literal
    let l := pair.appArg!              -- the literal
    let rest := terms.appArg!          -- remaining terms
    do
      let (e₁, h₁) ← reifyLiteral l
      if isNilExpr rest then
        .ok (e₁, mkApp4 (mkConst ``Sat.PB.Constr.Reify_cnf_one) pv l e₁ h₁)
      else
        let (e₂, h₂) ← reifyConstr1 rest
        .ok (mkApp2 (mkConst ``And) e₁ e₂,
         mkApp7 (mkConst ``Sat.PB.Constr.Reify_cnf_and) pv l e₁ rest e₂ h₁ h₂)
  /-- Reify a literal expression. -/
  reifyLiteral (l : Expr) : Except String (Expr × Expr) :=
    let n := l.appArg!
    let (e, h) := reifyVar n
    match l.appFn!.constName? with
    | some ``Sat.PB.Literal.pos =>
      .ok (mkApp (mkConst ``Not) e,
       mkApp4 (mkConst ``Sat.PB.Literal.Reify_pos) pv e n h)
    | some ``Sat.PB.Literal.neg =>
      .ok (e, mkApp4 (mkConst ``Sat.PB.Literal.Reify_neg) pv e n h)
    | some name => .error s!"buildReify.reifyLiteral: unexpected literal head '{name}'"
    | none => .error "buildReify.reifyLiteral: expression has no constant head"
  /-- Look up a variable in the quantifier context.
      Under `(a₀ ... a_{n-1} : Prop) (pv) (h₀ : pv 0 ↔ a₀) ... (h_{n-1})`:
      - `aᵢ` is at de Bruijn index `2*nvars - i`
      - `hᵢ` is at de Bruijn index `nvars - i - 1` -/
  reifyVar (v : Expr) : Expr × Expr :=
    let n := v.rawNatLit?.getD 0
    (mkBVar (2 * nvars - n), mkBVar (nvars - n - 1))

-- Top-level entry point

/-- Parse CNF + VeriPB proof and construct a proof of unsatisfiability.
    Returns (numVars, ctx, ctx', proof) where proof : PBFmla.proof ctx [].
    Adds auxiliary declarations to the environment. -/
def fromVeriPBAux (cnf proof : String) (name : Name) :
    MetaM (Nat × Expr × Expr × Expr) := do
  -- Parse CNF
  let formula ← match parseDimacs cnf with
    | .ok f => pure f
    | .error e => throwError "CNF parse error: {e}"
  if formula.clauses.isEmpty then throwError "empty CNF"
  -- Convert to PB constraints
  let pbArray ← formula.clauses.mapM fun clause =>
    match dimacsClauseToPB clause with
    | .ok c => pure c
    | .error e => throwError "clause conversion: {e}"
  -- Build formula expression (balanced tree)
  let ctx' ← match buildConj pbArray 0 pbArray.size with
    | .ok e => pure e
    | .error e => throwError "formula construction: {e}"
  -- Add as a definition for efficient kernel checking
  let ctxName := name ++ `ctx
  addDecl <| Declaration.defnDecl {
    name := ctxName
    levelParams := []
    type := mkConst ``Sat.PB.PBFmla
    value := ctx'
    hints := .regular 0
    safety := .safe
  }
  let ctx := mkConst ctxName
  -- Parse VeriPB proof
  let proofData ← match parseVeriPBProofWith { numVars := formula.numVars } proof with
    | .ok p => pure p
    | .error e => throwError "VeriPB parse error: {e}"
  -- Build the proof
  match buildProof pbArray ctx ctx' proofData.steps formula.numVars with
  | .ok proofExpr =>
    let proofName := name ++ `proof
    -- The proof type: ∀ v, PBFmla.allSat v ctx → False
    let proofType := mkForall `v .default (mkConst ``Sat.PB.Valuation) <|
      mkForall `hv .default (mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx) <|
        mkConst ``False
    addDecl <| Declaration.thmDecl {
      name := proofName
      levelParams := []
      type := proofType
      value := proofExpr
    }
    -- Build reified propositional theorem
    let (reifyType, reifyValue) ←
      match buildReify ctx ctx' (mkConst proofName) formula.numVars with
      | .ok r => pure r
      | .error e => throwError "reification: {e}"
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := reifyType
      value := reifyValue
    }
    return (formula.numVars, ctx, ctx', mkConst name)
  | .error e => throwError "proof construction failed: {e}"

/-- User-facing command: `veripb_proof name "cnf..." "proof..."` -/
elab "veripb_proof " n:ident ppSpace cnf:str ppSpace proof:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let cnfStr := cnf.getString
    let proofStr := proof.getString
    let (_nvars, _ctx, _ctx', _proof) ← fromVeriPBAux cnfStr proofStr name

/-- Term-level elaborator: `from_veripb "cnf..." "proof..."`.
    Produces the reified propositional theorem directly as a term.
    Usage: `theorem unsat : ... := from_veripb "p cnf ..." "pseudo-Boolean ..."` -/
elab "from_veripb " cnf:str ppSpace proof:str : term <= expectedType => do
  let cnfStr := cnf.getString
  let proofStr := proof.getString
  -- Use a fresh hygienic name for auxiliary declarations
  let name ← Lean.Elab.Term.mkAuxName `_veripb
  let (_nvars, _ctx, _ctx', proofConst) ← fromVeriPBAux cnfStr proofStr name
  -- Check that the produced type matches the expected type
  let proofType ← inferType proofConst
  unless (← isDefEq proofType expectedType) do
    throwError "from_veripb: proof type{indentExpr proofType}\n\
      does not match expected type{indentExpr expectedType}"
  return proofConst

/-- Command with file loading:
`veripb_proof_file name "path/to/cnf" "path/to/proof"`.
Reads CNF and proof files from disk at elaboration time. -/
elab "veripb_proof_file " n:ident ppSpace cnfPath:str ppSpace proofPath:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let cnfFile := System.FilePath.mk cnfPath.getString
    let proofFile := System.FilePath.mk proofPath.getString
    let cnfStr ← IO.FS.readFile cnfFile
    let proofStr ← IO.FS.readFile proofFile
    let (_nvars, _ctx, _ctx', _proof) ← fromVeriPBAux cnfStr proofStr name

/-- Term-level elaborator with file loading:
`from_veripb_file "path/to/cnf" "path/to/proof"`.
Reads CNF and proof files from disk at elaboration time. -/
elab "from_veripb_file " cnfPath:str ppSpace proofPath:str : term <= expectedType => do
  let cnfFile := System.FilePath.mk cnfPath.getString
  let proofFile := System.FilePath.mk proofPath.getString
  let cnfStr ← IO.FS.readFile cnfFile
  let proofStr ← IO.FS.readFile proofFile
  let name ← Lean.Elab.Term.mkAuxName `_veripb
  let (_nvars, _ctx, _ctx', proofConst) ← fromVeriPBAux cnfStr proofStr name
  let proofType ← inferType proofConst
  unless (← isDefEq proofType expectedType) do
    throwError "from_veripb_file: proof type\
      {indentExpr proofType}\n\
      does not match expected type{indentExpr expectedType}"
  return proofConst

-- Direct PB constraint entry point (no CNF parsing)

/-- Verify a VeriPB proof against PB constraints given directly.
    Returns (ctx, ctx', proofExpr) where proofExpr : ∀ v, allSat v ctx → False.
    Skips CNF parsing and reification — caller provides the constraints.
    Adds auxiliary declarations to the environment. -/
def fromVeriPBDirect (constrs : Array Sat.PB.Constr) (numVars : Nat)
    (proofStr : String) (name : Name) (vt : VarTable := {}) :
    MetaM (Expr × Expr × Expr) := do
  if constrs.isEmpty then throwError "empty constraint array"
  -- Build formula expression (balanced tree)
  let ctx' ← match buildConj constrs 0 constrs.size with
    | .ok e => pure e
    | .error e => throwError "formula construction: {e}"
  -- Add as a definition for efficient kernel checking
  let ctxName := name ++ `ctx
  addDecl <| Declaration.defnDecl {
    name := ctxName
    levelParams := []
    type := mkConst ``Sat.PB.PBFmla
    value := ctx'
    hints := .regular 0
    safety := .safe
  }
  let ctx := mkConst ctxName
  -- Parse VeriPB proof
  let proofData ← match parseVeriPBProofWith
      { vt with numVars := max vt.numVars numVars } proofStr with
    | .ok p => pure p
    | .error e => throwError "VeriPB parse error: {e}"
  -- Build the proof
  match buildProof constrs ctx ctx' proofData.steps numVars with
  | .ok proofExpr =>
    let proofName := name ++ `proof
    let proofType := mkForall `v .default (mkConst ``Sat.PB.Valuation) <|
      mkForall `hv .default
        (mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx) <|
        mkConst ``False
    addDecl <| Declaration.thmDecl {
      name := proofName
      levelParams := []
      type := proofType
      value := proofExpr
    }
    return (ctx, ctx', mkConst proofName)
  | .error e => throwError "proof construction failed: {e}"


-- OPB file parsing for native PB instances

/-- An OPB objective in minimization form with nonnegative coefficients:
`f = Σ coeff·lit + offset`. A `max:` objective is negated first, as VeriPB
does (`PBObjective::from_terms` with `is_maximization`), and a negative
coefficient `-a·l` becomes `a·¬l` with `-a` added to the offset. -/
structure OPBObjective where
  terms : List Sat.PB.Term
  offset : Int
  /-- The file had `max:` (the objective above is the negated one). -/
  fromMax : Bool := false
  deriving Repr

/-- A parsed OPB file. `names` lists the variables not written `x<N>` with
their indices. -/
structure OPBInstance where
  numVars : Nat
  constrs : Array Sat.PB.Constr
  objective : Option OPBObjective
  names : List (String × Nat)
  deriving Repr

/-- End-of-line marker in the OPB token stream. -/
private def opbEOL : String := "\n"

/-- Tokens of an OPB file: whitespace-separated, `;` on its own, a leading
relation (`>=`, `<=`, `=`) split off its number, `*` lines skipped, and
`opbEOL` after the tokens of every nonempty line (VeriPB reads one statement
per line). -/
private def opbTokens (s : String) : Array String := Id.run do
  let mut toks : Array String := #[]
  for line in s.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.isEmpty || t.startsWith "*" then continue
    for w in ((t.replace ";" " ; ").replace "\t" " ").splitOn " " do
      let w := w.trimAscii.toString
      if w.isEmpty then continue
      let rel := if w.startsWith ">=" then ">=" else if w.startsWith "<=" then "<="
        else if w.startsWith "=" then "=" else ""
      if !rel.isEmpty && w.length > rel.length then
        toks := toks.push rel
        toks := toks.push (w.drop rel.length).toString
      else
        toks := toks.push w
    toks := toks.push opbEOL
  return toks

/-- Byte `b` may occur after the first character of an OPB variable
(`[_a-zA-Z0-9\-^\[\]{}]`). -/
@[inline] private def opbVarByte (b : UInt8) : Bool :=
  (b ≥ 97 && b ≤ 122) || (b ≥ 65 && b ≤ 90) || (b ≥ 48 && b ≤ 57) ||
  b == 95 || b == 45 || b == 94 || b == 91 || b == 93 || b == 123 || b == 125

/-- `s` without its first `k` bytes is an OPB variable: VeriPB's `Var`
token `[a-zA-Z_][_a-zA-Z0-9\-^\[\]{}]+` (`opb_token.rs`). -/
private def opbVarAt (s : String) (k : Nat) : Bool := Id.run do
  let n := s.utf8ByteSize
  if k + 2 > n then return false
  let b := byteAt s k
  if !((b ≥ 97 && b ≤ 122) || (b ≥ 65 && b ≤ 90) || b == 95) then return false
  for i in [k + 1:n] do
    if !opbVarByte (byteAt s i) then return false
  return true

/-- Is an OPB token a literal (`name` or `~name`)? -/
private def opbIsLit (w : String) : Bool :=
  -- 126 = '~'
  opbVarAt w (if byteAt w 0 == 126 then 1 else 0)

/-- Is an OPB token a label `@[a-zA-Z0-9_^\[\]{}]+` (`opb_token.rs`)? -/
private def opbIsLabel (w : String) : Bool := Id.run do
  let n := w.utf8ByteSize
  -- 64 = '@'
  if n < 2 || byteAt w 0 != 64 then return false
  for i in [1:n] do
    let b := byteAt w i
    if !(opbVarByte b && b != 45) then return false
  return true

/-- Normalize `Σ cᵢ·lᵢ` (integer coefficients) to nonnegative coefficients;
returns the terms and the sum of the negative coefficients. -/
private def normIntTerms (terms : List (Int × Sat.PB.Literal)) :
    List Sat.PB.Term × Int :=
  let (ts, adj) := terms.foldl (init := (([] : List Sat.PB.Term), (0 : Int)))
    fun (acc, adj) (c, l) =>
      if c ≥ 0 then ((c.toNat, l) :: acc, adj)
      else (((-c).toNat, l.negate) :: acc, adj + c)
  (ts.reverse, adj)

/-- Parse an OPB file (PB competition format, as VeriPB's `opb_parser.rs`):
`*` comment lines, an optional `min:`/`max:` objective with an optional
constant, constraints with `>=`, `<=` or `=` (an `=` constraint becomes its
`≥` part followed by its `≤` part, which keeps VeriPB's constraint IDs),
optional `@label` prefixes, and variable names matching VeriPB's `Var`
token (see the module doc for the index assignment). Integers are
`[+-]?[0-9]+`. Each statement is on one line of its own and ends with `;`;
any other token is a parse error. A negative right-hand side is clamped to
`0` after the adjustment for negative coefficients. -/
def parseOPBNamed (s : String) : Except String OPBInstance := do
  let toks := opbTokens s
  -- Pass 1: largest x<N> index, then named variables in order of appearance.
  let mut maxX := 0
  for w in toks do
    if opbIsLit w then
      let v := if w.startsWith "~" then (w.drop 1).toString else w
      if let some i := canonXIndex? v then maxX := max maxX (i + 1)
  let mut names : Std.HashMap String Nat := {}
  let mut order : Array (String × Nat) := #[]
  let mut nv := maxX
  for w in toks do
    if opbIsLit w then
      let v := if w.startsWith "~" then (w.drop 1).toString else w
      if (canonXIndex? v).isNone && !names.contains v then
        names := names.insert v nv
        order := order.push (v, nv)
        nv := nv + 1
  let lit (w : String) : Except String Sat.PB.Literal := do
    if w == opbEOL then throw "OPB parse: statement ends before ';'"
    if !opbIsLit w then throw s!"OPB parse: expected a literal, got '{w}'"
    let (neg, v) := if w.startsWith "~" then (true, (w.drop 1).toString) else (false, w)
    let i ← match canonXIndex? v with
      | some i => pure i
      | none => match names[v]? with
        | some i => pure i
        | none => throw s!"OPB parse: bad var '{w}'"
    return if neg then .neg i else .pos i
  let int (w : String) : Except String Int :=
    if w == opbEOL then .error "OPB parse: statement ends before ';'"
    else match parseCoeffInt w with
    | .ok c => .ok c
    | .error _ => .error s!"OPB parse: bad coeff '{w}'"
  -- a statement ends with `;` and the end of its line
  let endStmt (pos : Nat) : Except String Unit := do
    let t := toks.getD pos opbEOL
    if t != ";" then
      throw s!"OPB parse: expected ';', got '{if t == opbEOL then "end of line" else t}'"
    if toks.getD (pos + 1) opbEOL != opbEOL then
      throw s!"OPB parse: more than one statement on a line \
        (unexpected '{toks.getD (pos + 1) ""}' after ';')"
  -- Pass 2: statements, one per line.
  let mut pos := 0
  let mut constrs : Array Sat.PB.Constr := #[]
  let mut objective : Option OPBObjective := none
  let n := toks.size
  while pos < n do
    let w := toks[pos]!
    if w == "min:" || w == "max:" then
      let isMax := w == "max:"
      pos := pos + 1
      let mut terms : List (Int × Sat.PB.Literal) := []
      let mut constant : Int := 0
      while toks.getD pos ";" != ";" do
        let c ← int toks[pos]!
        pos := pos + 1
        let t := toks.getD pos ";"
        if t == ";" then constant := c
        else
          terms := (c, ← lit t) :: terms
          pos := pos + 1
      endStmt pos
      pos := pos + 2
      let sgn : Int := if isMax then -1 else 1
      let (ts, adj) := normIntTerms (terms.reverse.map fun (c, l) => (sgn * c, l))
      objective := some { terms := ts, offset := sgn * constant + adj, fromMax := isMax }
    else
      if w.startsWith "@" then
        if !opbIsLabel w then throw s!"OPB parse: bad label '{w}'"
        pos := pos + 1
      let mut terms : List (Int × Sat.PB.Literal) := []
      while !([">=", "<=", "="].contains (toks.getD pos ">=")) do
        let c ← int toks[pos]!
        let l ← lit (toks.getD (pos + 1) "")
        terms := (c, l) :: terms
        pos := pos + 2
      let rel := toks.getD pos ""
      let d ← int (toks.getD (pos + 1) "")
      endStmt (pos + 2)
      pos := pos + 4
      let fwd := terms.reverse
      let geq : Sat.PB.Constr :=
        let (ts, adj) := normIntTerms fwd
        ⟨ts, (d - adj).toNat⟩
      let leq : Sat.PB.Constr :=
        let (ts, adj) := normIntTerms (fwd.map fun (c, l) => (-c, l))
        ⟨ts, (-d - adj).toNat⟩
      if rel == ">=" then constrs := constrs.push geq
      else if rel == "<=" then constrs := constrs.push leq
      else constrs := (constrs.push geq).push leq
  return { numVars := nv, constrs, objective, names := order.toList }

/-- Parse an OPB file into variable count, constraints and objective
(nonnegative literal terms plus an integer offset). -/
def parseOPBWithObj (s : String) :
    Except String (Nat × Array Sat.PB.Constr × Option OPBObjective) := do
  let inst ← parseOPBNamed s
  .ok (inst.numVars, inst.constrs, inst.objective)

/-- Parse an OPB file into an array of PB constraints and variable count
(the objective is dropped). -/
def parseOPB (s : String) : Except String (Nat × Array Sat.PB.Constr) := do
  let inst ← parseOPBNamed s
  .ok (inst.numVars, inst.constrs)

-- Command: load OPB + proof files, verify, register theorem
-- `opb_veripb_file name "path/to/opb" "path/to/proof"`
elab "opb_veripb_file " n:ident ppSpace
    opbPath:str ppSpace proofPath:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let opbStr ← IO.FS.readFile (System.FilePath.mk opbPath.getString)
    let proofStr ← IO.FS.readFile
      (System.FilePath.mk proofPath.getString)
    let inst ← match parseOPBNamed opbStr with
      | .ok r => pure r
      | .error e => throwError "OPB parse error: {e}"
    let (_ctx, _ctx', _proof) ←
      fromVeriPBDirect inst.constrs inst.numVars proofStr name
        (VarTable.ofList inst.names inst.numVars)
    Lean.logInfo m!"Registered {name} (OPB: {inst.numVars} vars, \
      {inst.constrs.size} constraints, fully verified)"

end PBCatcher
