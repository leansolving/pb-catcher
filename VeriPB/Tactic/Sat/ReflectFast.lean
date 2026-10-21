/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.ReflectCheck

/-!
# Fast reflection checker (runtime replacement)

Runtime implementation of the verified reflection checker
(`VeriPB.Reflect.checkProofBool`, see `Reflect.lean`), installed via
`@[implemented_by Fast.checkProofBoolFast]`. Nothing in this file is used
by any proof.

**Extensional equality is the trust requirement.** The `nativeEqTrue` axiom
produced by `veripb_reflect` asserts that the *verified* `checkProofBool`
returns `true`; the code here must therefore accept exactly the proofs the
verified definition accepts. Every operation below mirrors its verified
counterpart in `ReflectCheck.lean` step by step, including term order:
normalization happens at the same points, produces the same term order
(`VeriPB.normalizeArrays` is an exact simulation of `VeriPB.normalizeConstr`),
weakening normalizes and then removes every term of the variable, and RUP
propagation makes the same single pass over the same hint constraints.

**Representation.** A constraint is stored as two parallel `Array Nat`
fields: coefficients and literal codes (`2*v` for `x_v`, `2*v+1` for
`¬x_v`). Small `Nat`s are unboxed scalars in the Lean runtime, so this
avoids the per-term heap objects of `List (Nat × Literal)`.
-/

namespace VeriPB.Reflect.Fast

/-- Literal code of a `Sat.PB.Literal` (`2*v` positive, `2*v+1` negative): the
encoding `VeriPB.normalizeArrays` is specified against. -/
abbrev encLit : Sat.PB.Literal → Nat := VeriPB.litCode

/-- Inverse of `encLit`. -/
abbrev decLit : Nat → Sat.PB.Literal := VeriPB.litOfCode

/-- Constraint `Σ coeffs[i] * lit(lits[i]) ≥ degree` in parallel-array form.

`split` records structural knowledge used to pick a cheap exact
normalization path. A *block* is a term range with no zero coefficient, no
repeated literal and no complementary pair; the verified normalizer is the
identity on a block. The encoding is:
* `split = 0`: nothing known (general normalization);
* `0 < split = coeffs.size`: the whole term list is one block;
* `0 < split < coeffs.size`: `[0, split)` and `[split, size)` are both blocks
  (the result of adding two normalized constraints).
Every operation below maintains this invariant; it is never assumed without
having been established by `normalizeFConstr`, `blockOf`, or an operation
that provably preserves it. -/
structure FConstr where
  coeffs : Array Nat
  lits : Array Nat
  degree : Nat
  split : Nat := 0
  deriving Inhabited

/-- Checker state: constraint database plus bookkeeping. -/
structure FBoolCheckState where
  db : Std.HashMap Nat FConstr
  origConstrs : Array Constr
  objective : Objective
  best : Option Nat
  offset : Int := 0
  nextId : Nat
  numVars : Nat
  formulaSize : Nat
  coreIds : Std.HashSet Nat := {}
  s2c : Bool := false
  deriving Inhabited

/-- `true` iff the term list is a block: no zero coefficient, no repeated
literal, no complementary pair. -/
def isBlock (coeffs lits : Array Nat) : Bool := Id.run do
  let n := coeffs.size
  if n == 0 then return true
  let mut maxLit := 0
  for i in [:n] do
    if coeffs[i]! == 0 then return false
    if lits[i]! > maxLit then maxLit := lits[i]!
  if maxLit + 2 > n * n + 8 then
    -- sparse literal codes: pairwise scan instead of a bitmap
    for i in [:n] do
      let v := lits[i]! / 2
      for j in [i+1:n] do
        if lits[j]! / 2 == v then return false
    return true
  let mut seen : Array Bool := Array.replicate (maxLit + 2) false
  for i in [:n] do
    let l := lits[i]!
    if seen[l]! || seen[l ^^^ 1]! then return false
    seen := seen.set! l true
  return true

/-- `split` value for a term list: `size` if it is a block, else `0`. -/
def blockOf (coeffs lits : Array Nat) : Nat :=
  if isBlock coeffs lits then coeffs.size else 0

def toFConstr (c : Constr) : FConstr :=
  let ts := c.terms.toArray
  let coeffs := ts.map (·.1)
  let lits := ts.map (encLit ·.2)
  ⟨coeffs, lits, c.degree, blockOf coeffs lits⟩

def fromFConstr (c : FConstr) : Constr := Id.run do
  let mut terms : List Sat.PB.Term := []
  for k in [:c.coeffs.size] do
    let i := c.coeffs.size - 1 - k
    terms := (c.coeffs[i]!, decLit c.lits[i]!) :: terms
  return ⟨terms, c.degree⟩

def FConstr.coeffSum (c : FConstr) : Nat :=
  c.coeffs.foldl (· + ·) 0

def FConstr.isContra (c : FConstr) : Bool :=
  c.coeffSum < c.degree

/-- Negate with a precomputed coefficient sum `cs`. Flipping every literal
keeps blocks blocks. -/
def FConstr.negateWith (c : FConstr) (cs : Nat) : FConstr :=
  ⟨c.coeffs, c.lits.map (· ^^^ 1), cs - c.degree + 1, c.split⟩

def FConstr.negate (c : FConstr) : FConstr :=
  c.negateWith c.coeffSum

/-- Second half of `rupNegateF` (mirrors `VeriPB.Reflect.rupNegate`) on an
already normalized constraint: negate, or the negated terms with degree `0`
when the target is contradictory on its own. -/
def rupNegateWith (nf : FConstr) : FConstr :=
  let cs := nf.coeffSum
  if nf.degree ≤ cs then nf.negateWith cs
  else ⟨nf.coeffs, nf.lits.map (· ^^^ 1), 0, nf.split⟩

/-- Concatenation (mirrors `VeriPB.addConstrs`). Two blocks give a two-block
constraint; anything else loses the structure. -/
def addFConstrs (c1 c2 : FConstr) : FConstr :=
  let n1 := c1.coeffs.size
  let n2 := c2.coeffs.size
  let split :=
    if n1 == 0 then c2.split
    else if n2 == 0 then c1.split
    else if c1.split == n1 && c2.split == n2 then n1
    else 0
  ⟨c1.coeffs ++ c2.coeffs, c1.lits ++ c2.lits, c1.degree + c2.degree, split⟩

/-- Scaling by `k > 0` keeps blocks blocks (no zeros, literals unchanged,
a blocked pair stays blocked); `k = 0` zeroes everything. -/
def mulFConstr (c : FConstr) (k : Nat) : FConstr :=
  ⟨c.coeffs.map (k * ·), c.lits, k * c.degree, if k == 0 then 0 else c.split⟩

/-- Ceiling division by `k > 0` keeps positive coefficients positive. Only
applied to normalized inputs, which have no complementary pair, so blocks
stay blocks. -/
def divFConstr (c : FConstr) (k : Nat) : FConstr :=
  ⟨c.coeffs.map (Sat.PB.ceilDiv · k), c.lits, Sat.PB.ceilDiv c.degree k,
    if k == 0 then 0 else c.split⟩

/-- Saturation keeps blocks blocks unless the degree is `0`, which zeroes
every coefficient. -/
def saturateFConstr (c : FConstr) : FConstr :=
  ⟨c.coeffs.map (min · c.degree), c.lits, c.degree,
    if c.degree == 0 then 0 else c.split⟩

/-- Remove every term of variable `varIdx` and subtract the removed
coefficients from the degree, truncated at 0 (mirrors
`VeriPB.weakenConstr`; the caller normalizes first, as the verified
`execPolOne` does). Removing terms from a block leaves a block, so the
structural flag is adjusted rather than dropped. -/
def weakenFConstr (c : FConstr) (varIdx : Nat) : FConstr := Id.run do
  let n := c.lits.size
  let mut cs : Array Nat := Array.mkEmpty n
  let mut ls : Array Nat := Array.mkEmpty n
  let mut removed := 0
  let mut removedBefore := 0  -- removed terms with index < c.split
  for i in [:n] do
    if c.lits[i]! / 2 == varIdx then
      removed := removed + c.coeffs[i]!
      if i < c.split then removedBefore := removedBefore + 1
    else
      cs := cs.push c.coeffs[i]!
      ls := ls.push c.lits[i]!
  let split := if c.split == 0 then 0 else c.split - removedBefore
  return ⟨cs, ls, c.degree - removed, split⟩

/-- Rebuild a constraint from per-term coefficients `cs'` over the literals
`c.lits`, dropping the zero coefficients (`Sat.PB.stripZero`). The literals
of the kept terms are a subset of `c.lits`, so a block stays a block. -/
def stripZeroF (c : FConstr) (cs' : Array Nat) (degree : Nat) : FConstr := Id.run do
  let n := c.lits.size
  let mut cs : Array Nat := Array.mkEmpty n
  let mut ls : Array Nat := Array.mkEmpty n
  for i in [:n] do
    let a := cs'[i]!
    if a != 0 then
      cs := cs.push a
      ls := ls.push c.lits[i]!
  let split := if n != 0 && c.split == n then cs.size else 0
  return ⟨cs, ls, degree, split⟩

/-- Mirrors `Sat.PB.cgDivConstr` (`k c`). Literal code `2v+1` is negated. -/
def cgDivFConstr (c : FConstr) (k : Nat) : FConstr := Id.run do
  let n := c.lits.size
  let mut cs : Array Nat := Array.mkEmpty n
  let mut off := 0
  for i in [:n] do
    let a := c.coeffs[i]!
    if c.lits[i]! % 2 == 1 then
      cs := cs.push (a / k)
      off := off + a % k
    else
      cs := cs.push (Sat.PB.ceilDiv a k)
  return stripZeroF c cs (Sat.PB.ceilDiv (c.degree - off) k)

/-- Mirrors `Sat.PB.mirConstr` (`k n`). -/
def mirFConstr (c : FConstr) (k : Nat) : FConstr :=
  let r := c.degree % k
  stripZeroF c (c.coeffs.map (Sat.PB.mirF k r ·)) (Sat.PB.ceilDiv c.degree k * r)

/-- Mirrors `Sat.PB.mirVarConstr` (`k m`). -/
def mirVarFConstr (c : FConstr) (k : Nat) : FConstr := Id.run do
  let n := c.lits.size
  let mut off := 0
  for i in [:n] do
    if c.lits[i]! % 2 == 1 then
      off := off + Sat.PB.mirShift k c.coeffs[i]!
  let d := c.degree + off
  let r := d % k
  let mut cs : Array Nat := Array.mkEmpty n
  let mut mins := 0
  for i in [:n] do
    let a := c.coeffs[i]!
    if c.lits[i]! % 2 == 1 then
      let m := min (Sat.PB.mirShift k a) r
      cs := cs.push (Sat.PB.ceilDiv a k * r - m)
      mins := mins + m
    else
      cs := cs.push (Sat.PB.mirF k r a)
  return stripZeroF c cs (Sat.PB.mirF k r d - mins)

/-- General exact normalization through `VeriPB.normalizeArraysCore`; the
result is flagged as a block when the one-pass path completed. -/
def normalizeGeneralF (c : FConstr) : FConstr :=
  let (cs, ls, d, isBlk) := VeriPB.normalizeArraysCore c.coeffs c.lits c.degree
  ⟨cs, ls, d, if isBlk then cs.size else blockOf cs ls⟩

/-- Exact normalization of a two-block constraint (see `FConstr.split`).

On `c1 ++ c2` with both parts blocks, the verified normalizer
(`VeriPB.normalizeConstr`) proceeds as follows: for each term of `c1` in
order, its only possible complement is the unique term of `c2` with the
opposite literal; if `min ≤ degree` the pair is cancelled and the degree
reduced, otherwise the process is blocked (handled by the general
algorithm). No term of `c2` has a complement after it. Then like terms are
merged into their first occurrence, i.e. each `c2` term whose literal occurs
in `c1` is added to that `c1` term. The result lists the surviving `c1`
terms in order, then the surviving `c2` terms in order. A blocked pair, or
sparse literal codes, fall back to `VeriPB.normalizeArraysCore` on the
unmodified constraint; partial cancellations are discarded. -/
def normalizeTwoBlocks (c : FConstr) : FConstr := Id.run do
  let n := c.coeffs.size
  let split := c.split
  let n2 := n - split
  let mut maxLit := 0
  for i in [:n] do
    if c.lits[i]! > maxLit then maxLit := c.lits[i]!
  if maxLit + 2 > n * n + 8 then
    return normalizeGeneralF c
  let noIdx := n
  -- index of each c2 literal
  let mut idx : Array Nat := Array.replicate (maxLit + 2) noIdx
  for j in [split:n] do
    idx := idx.set! c.lits[j]! j
  -- remaining c2 coefficients after cancellation / merging (0 = consumed)
  let mut rem : Array Nat := Array.mkEmpty n2
  for j in [split:n] do
    rem := rem.push c.coeffs[j]!
  let mut deg := c.degree
  let mut outC : Array Nat := Array.mkEmpty n
  let mut outL : Array Nat := Array.mkEmpty n
  for i in [:split] do
    let l := c.lits[i]!
    let mut a := c.coeffs[i]!
    let j := idx[l ^^^ 1]!
    if j != noIdx then
      let b := rem[j - split]!
      let m := min a b
      if m > deg then
        -- blocked cancellation: replay the full process exactly
        return normalizeGeneralF c
      a := a - m
      rem := rem.set! (j - split) (b - m)
      deg := deg - m
    if a > 0 then
      let j' := idx[l]!
      if j' != noIdx then
        a := a + rem[j' - split]!
        rem := rem.set! (j' - split) 0
      outC := outC.push a
      outL := outL.push l
  for j in [split:n] do
    let b := rem[j - split]!
    if b > 0 then
      outC := outC.push b
      outL := outL.push c.lits[j]!
  return ⟨outC, outL, deg, outC.size⟩

/-- Exact simulation of `VeriPB.normalizeConstr`, dispatching on the known
structure: identity on a block, linear merge for two blocks, otherwise the
general algorithm `VeriPB.normalizeArraysCore`. -/
def normalizeFConstr (c : FConstr) : FConstr :=
  let n := c.coeffs.size
  if c.split == 0 || n == 0 then normalizeGeneralF c
  else if c.split == n then c
  else normalizeTwoBlocks c

/-- Mirrors `VeriPB.Reflect.rupNegate`. -/
def rupNegateF (c : FConstr) : FConstr :=
  rupNegateWith (normalizeFConstr c)

/-! ### Pol RPN -/

inductive FStackElem where
  | constr : FConstr → FStackElem
  | nat : Nat → FStackElem

def execFPolOne (db : Std.HashMap Nat FConstr)
    (stack : List FStackElem) (op : VeriPB.PolOp) :
    Option (List FStackElem) :=
  match op with
  | .pushId id => match db[id]? with
    | some c => some (.constr c :: stack)
    | none => none
  | .pushNat n => some (.nat n :: stack)
  | .pushLitAxiom lit => match VeriPB.opbLitToPB lit with
    | .ok pbLit => some (.constr ⟨#[1], #[encLit pbLit], 0, 1⟩ :: stack)
    | .error _ => none
  | .add => match stack with
    | .constr c2 :: .constr c1 :: rest =>
      some (.constr (addFConstrs c1 c2) :: rest)
    | _ => none
  | .mul => match stack with
    | .nat k :: .constr c :: rest =>
      some (.constr (mulFConstr c k) :: rest)
    | _ => none
  | .div => match stack with
    | .nat k :: .constr c :: rest =>
      if k == 0 then none
      else some (.constr (divFConstr (normalizeFConstr c) k) :: rest)
    | _ => none
  | .saturate => match stack with
    | .constr c :: rest =>
      some (.constr (saturateFConstr (normalizeFConstr c)) :: rest)
    | _ => none
  | .weaken varName => match stack with
    | .constr c :: rest =>
      if varName.startsWith "x" then
        match (varName.drop 1).toString.toNat? with
        | some n => if n > 0 then
            some (.constr (weakenFConstr (normalizeFConstr c) (n - 1)) :: rest)
          else none
        | none => none
      else none
    | _ => none
  | .lowerRhs => match stack with
    | .nat k :: .constr c :: rest =>
      -- lowering the degree keeps the term structure (and the block flag)
      let nc := normalizeFConstr c
      some (.constr { nc with degree := nc.degree - k } :: rest)
    | _ => none
  | .divVar => match stack with
    | .nat k :: .constr c :: rest =>
      if k == 0 then none
      else some (.constr (cgDivFConstr (normalizeFConstr c) k) :: rest)
    | _ => none
  | .mir => match stack with
    | .nat k :: .constr c :: rest =>
      if k == 0 then none
      else some (.constr (mirFConstr (normalizeFConstr c) k) :: rest)
    | _ => none
  | .mirVar => match stack with
    | .nat k :: .constr c :: rest =>
      if k == 0 then none
      else some (.constr (mirVarFConstr (normalizeFConstr c) k) :: rest)
    | _ => none

def execFPolOps (db : Std.HashMap Nat FConstr) :
    List VeriPB.PolOp → List FStackElem → Option (List FStackElem)
  | [], stack => some stack
  | op :: rest, stack =>
    match execFPolOne db stack op with
    | some s => execFPolOps db rest s
    | none => none

def execFPolRPNBool (ops : List VeriPB.PolOp)
    (db : Std.HashMap Nat FConstr) : Option FConstr :=
  match execFPolOps db ops [] with
  | some [.constr c] => some c
  | _ => none

/-! ### RUP verification (unit propagation)

Mirrors `VeriPB.Reflect.verifyRupBool`: the same resolved hint list in the
same order (no implicit `~`, all ids resolved first), the same assignment
size `varBound hs`, ONE pass over the hints, the same slack, and within a
constraint the same forced literals applied in term order. The accepted set
equals the verified one by construction: both run the same single pass, so
no confluence argument is needed. The assignment is a `ByteArray` indexed by
variable (`0` unassigned, `1` true, `2` false), so a literal with code
`2v + p` is true iff `asgn[v] = p + 1` and false iff `asgn[v] = 2 - p`.

Within one constraint the verified checker computes the forced literals
(unassigned, coefficient above the slack) before assigning any of them and
reports a conflict when a forced literal is already false at its turn. Here
the second pass decides "unassigned at the start of this constraint" on the
fly: the only variables that change during the pass are those it assigns
(`setVars`), so a currently assigned literal was forced iff its variable is
in `setVars`; a forced literal that is now false is a conflict, every other
assigned literal is skipped, exactly as in `assignLits`. -/

/-- `1 +` the largest variable of the constraints (`0` if none); mirrors
`varBound`. -/
def varBoundF (hs : Array FConstr) : Nat := Id.run do
  let mut m := 0
  for c in hs do
    for l in c.lits do
      if l / 2 + 1 > m then m := l / 2 + 1
  return m

/-- Value of variable `v` (`0` unassigned, also out of range). -/
@[inline] def asgnGet (asgn : ByteArray) (v : Nat) : UInt8 :=
  if h : v < asgn.size then asgn[v] else 0

/-- One unit-propagation pass over `hs` in order from the empty assignment
of `n` variables: `true` iff it reaches a conflict (mirrors
`(propagateRound (Array.replicate n none) false hs).isNone`). -/
def rupConflictF (hs : Array FConstr) (n : Nat) : Bool := Id.run do
  let mut asgn : ByteArray := ByteArray.emptyWithCapacity n
  for _ in [:n] do
    asgn := asgn.push 0
  for c in hs do
    let k := c.lits.size
    -- pass 1: active sum (literals not false) and the largest coefficient
    -- of an unassigned literal
    let mut act := 0
    let mut maxUn := 0
    for i in [:k] do
      let l := c.lits[i]!
      let x := asgnGet asgn (l / 2)
      let p := (l % 2).toUInt8
      if x != 2 - p then
        let a := c.coeffs[i]!
        act := act + a
        if x == 0 && a > maxUn then maxUn := a
    if act < c.degree then return true
    let slack := act - c.degree
    if maxUn > slack then
      -- pass 2: assign the forced literals in term order
      let mut setVars : List Nat := []
      for i in [:k] do
        if c.coeffs[i]! > slack then
          let l := c.lits[i]!
          let v := l / 2
          let p := (l % 2).toUInt8
          let x := asgnGet asgn v
          if x == 0 then
            if v < asgn.size then asgn := asgn.set! v (p + 1)
            setVars := v :: setVars
          else if x == 2 - p && setVars.contains v then return true
  return false

/-- Mirrors `resolveHints`: `none` if an id is not in the database. -/
def rupFHintConstrs (negConstr : FConstr) (hints : List VeriPB.RupHint)
    (db : Std.HashMap Nat FConstr) : Option (Array FConstr) := Id.run do
  let mut arr : Array FConstr := Array.mkEmpty hints.length
  for h in hints do
    match h with
    | .negC => arr := arr.push negConstr
    | .id n => match db[n]? with
      | some c => arr := arr.push c
      | none => return none
  return some arr

/-- Mirrors `verifyRupBool` (`numVars` is unused). -/
def verifyFRupBool (negConstr : FConstr)
    (hints : List VeriPB.RupHint) (db : Std.HashMap Nat FConstr)
    (_numVars : Nat) : Bool :=
  match rupFHintConstrs negConstr hints db with
  | none => false
  | some hs => rupConflictF hs (varBoundF hs)

/-! ### Step execution -/

def FBoolCheckState.fromConstrs (constrs : Array Constr)
    (numVars : Nat) (objective : Objective) (offset : Int := 0) :
    FBoolCheckState :=
  { db := constrs.foldl (fun (db, i) c =>
      (db.insert i (toFConstr c), i + 1)) ({}, 1) |>.1
    origConstrs := constrs
    objective := objective
    best := none
    offset := offset
    nextId := constrs.size + 1
    numVars := numVars
    formulaSize := constrs.size
    coreIds := (List.range constrs.size).foldl (fun s i => s.insert (i + 1)) {}
    s2c := false }

/-- Mirrors `allIds`. -/
def allIdsF (db : Std.HashMap Nat FConstr) : Std.HashSet Nat :=
  db.keys.foldl (fun s id => s.insert id) {}

/-- Mirrors `allCore`. -/
def allCoreF (s : FBoolCheckState) : Bool :=
  s.db.keys.all fun id => s.coreIds.contains id

/-- Mirrors `impliesSyntactic` on `fromFConstr S` and `fromFConstr T`: the
target's literals are looked up in a hash map (first occurrence, as
`coeffOf`), and the source's literals are checked for repetition with a hash
set unless the source is flagged as a block (which has no repeated
literal). -/
def impliesSyntacticF (S T : FConstr) : Bool := Id.run do
  let B := T.degree
  if B == 0 then return true
  if S.coeffSum < S.degree then return true
  let mut tmap : Std.HashMap Nat Nat := {}
  for i in [:T.lits.size] do
    let l := T.lits[i]!
    if !tmap.contains l then tmap := tmap.insert l T.coeffs[i]!
  let isBlk := S.split != 0 && S.split == S.coeffs.size
  let mut seen : Std.HashSet Nat := {}
  let mut cost := 0
  for i in [:S.lits.size] do
    let l := S.lits[i]!
    if !isBlk then
      if seen.contains l then return false
      seen := seen.insert l
    let sc := S.coeffs[i]!
    match tmap[l]? with
    | none => cost := cost + sc
    | some t => if t < sc && t < B then cost := cost + (sc - t)
  return decide (B + cost ≤ S.degree)

/-- Mirrors `checkSolution`: the same literal conversion, with the valuation
`solValuation` stored as the hash set of the variables whose positive
literal is listed (a variable is true iff it is in the set). -/
def checkSolutionF (F : Array Constr) (obj : Objective)
    (lits : List VeriPB.OPBLit) : Option Nat :=
  match lits.mapM VeriPB.opbLitToPB with
  | .error _ => none
  | .ok pl =>
    let trueVars : Std.HashSet Nat := pl.foldl (fun s l => match l with
      | .pos i => s.insert i
      | .neg _ => s) {}
    let val : Sat.PB.Literal → Nat := fun l => match l with
      | .pos i => if trueVars.contains i then 1 else 0
      | .neg i => if trueVars.contains i then 0 else 1
    let evalS (ts : List Sat.PB.Term) : Nat :=
      ts.foldl (fun acc (a, l) => acc + a * val l) 0
    if F.all (fun c => decide (c.degree ≤ evalS c.terms)) then some (evalS obj)
    else none

/-- Mirrors `redGoalOf` (the goal database holds `FConstr`s). -/
def redGoalOfF (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (obj : Objective) (goalDb : Std.HashMap Nat FConstr) (gid : String) :
    Option Constr :=
  if gid == "#1" then some (substGoal subst C)
  else if gid == "#2" then
    if obj.isEmpty then none else some (objGoalConstr subst obj)
  else if gid.startsWith "#" then none
  else match gid.toNat? with
    | some n => (goalDb[n]?).map fun c => substGoal subst (fromFConstr c)
    | none => none

/-- Mirrors the database-goal part of `checkRedundance`
(`goalDb.toList.all (dbGoalCovered ...)`): constraints whose touched literals
are all set true are skipped on the array form; the rest are converted, and
the normalized database for the "already in the database" test is built
only when needed. -/
def dbGoalsCoveredF (subst : List (Nat × Sat.PB.SubstVal)) (nC : Constr)
    (goalDb : Std.HashMap Nat FConstr) (proved : List (String × Constr)) :
    Bool := Id.run do
  -- first binding wins, as `lookupSubst`
  let substMap : Std.HashMap Nat Sat.PB.SubstVal :=
    subst.foldl (fun m (v, sv) => if m.contains v then m else m.insert v sv) {}
  let mut remaining : Array FConstr := #[]
  for (_, c) in goalDb.toList do
    let mut allTrue := true
    for l in c.lits do
      let ok := match substMap[l / 2]? with
        | none => true
        | some .one => l % 2 == 0
        | some .zero => l % 2 == 1
        | some _ => false
      if !ok then
        allTrue := false
        break
    if !allTrue then remaining := remaining.push c
  if remaining.isEmpty then return true
  let normDb : List Constr := goalDb.toList.map fun (_, c) =>
    fromFConstr (normalizeFConstr c)
  for c in remaining do
    let D := fromFConstr c
    let G := substGoal subst D
    let ok := trivialByPair G ||
      impliesSyntactic (VeriPB.normalizeConstr D) G ||
       impliesSyntactic nC G ||
      proved.any (fun p => !p.1.startsWith "#" && constrMatchNorm G p.2) ||
      (let nG := VeriPB.normalizeConstr G
       normDb.any fun d => constrMatchNorm nG d)
    if !ok then return false
  return true

/-- Mirrors `processRedItems`. -/
def processFRedItems
    (execFn : FBoolCheckState → List VeriPB.ProofStep → Option FBoolCheckState)
    (goalOf : String → Option Constr) :
    FBoolCheckState → List VeriPB.ProofStep → List (String × Constr) →
      Option (FBoolCheckState × List (String × Constr))
  | st, [], proved => some (st, proved)
  | st, item :: rest, proved =>
    match item with
    | .proofgoal gid steps (some h) =>
      if steps.any innerStepForbidden then none else
      match goalOf gid with
      | none => none
      | some G =>
        let sub := { st with
          db := st.db.insert st.nextId (toFConstr (negTriv G))
          nextId := st.nextId + 1 }
        match execFn sub steps.toList with
        | none => none
        | some fin =>
          match fin.db[h]? with
          | some c =>
            if c.isContra then
              processFRedItems execFn goalOf { st with nextId := fin.nextId } rest
                ((gid, G) :: proved)
            else none
          | none => none
    | _ =>
      if isLStep item then
        match execFn st [item] with
        | some st' => processFRedItems execFn goalOf st' rest proved
        | none => none
      else none

/-- Mirrors `checkRedundance`. -/
def checkFRedundance
    (execFn : FBoolCheckState → List VeriPB.ProofStep → Option FBoolCheckState)
    (st0 : FBoolCheckState) (goalDb : Std.HashMap Nat FConstr)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List VeriPB.ProofStep) (qedHint : Option Nat) : Option Nat :=
  let nC := rupNegate C
  let st1 := { st0 with
    db := st0.db.insert st0.nextId (rupNegateF (toFConstr C))
    nextId := st0.nextId + 1 }
  match processFRedItems execFn (redGoalOfF subst C st0.objective goalDb) st1
      items [] with
  | none => none
  | some (fin, proved) =>
    let ok := match qedHint with
      | some cid => match fin.db[cid]? with
        | some c => c.isContra
        | none => false
      | none =>
        hashGoalsCovered subst C nC st0.objective proved &&
        dbGoalsCoveredF subst nC goalDb proved
    if ok then some fin.nextId else none

/-- Mirrors `redStep`. -/
def redFStep
    (execFn : FBoolCheckState → List VeriPB.ProofStep → Option FBoolCheckState)
    (state : FBoolCheckState) (constr : VeriPB.OPBConstr)
    (substPairs : List (String × String)) (items : List VeriPB.ProofStep)
    (qedHint : Option Nat) : Option FBoolCheckState :=
  match VeriPB.opbConstrToPB constr with
  | .error _ => none
  | .ok C =>
    match VeriPB.parseSubstPairs substPairs state.numVars with
    | .error _ => none
    | .ok subst =>
      match checkFRedundance execFn state state.db subst C items qedHint with
      | none => none
      | some fid =>
        some { state with
          db := state.db.insert fid (normalizeFConstr (toFConstr C))
          nextId := fid + 1
          coreIds := if state.s2c then state.coreIds.insert fid else state.coreIds }

/-- Mirrors `delcCheckedStep`. -/
def delcCheckedFStep
    (execFn : FBoolCheckState → List VeriPB.ProofStep → Option FBoolCheckState)
    (state : FBoolCheckState) (ids : List Nat)
    (substPairs : List (String × String))
    (sub : Option (Array VeriPB.ProofStep × Option Nat)) :
    Option FBoolCheckState :=
  match ids, sub with
  | [did], some (items, qedHint) =>
    match VeriPB.parseSubstPairs substPairs state.numVars with
    | .error _ => none
    | .ok subst =>
      if state.s2c && qedHint.isNone then none
      else if !state.coreIds.contains did then none
      else match state.db[did]? with
        | none => none
        | some D =>
          let rest := state.db.erase did
          let core' := state.coreIds.erase did
          let coreDb := rest.filter fun id _ => core'.contains id
          match checkFRedundance execFn
              { state with db := coreDb, coreIds := core' } coreDb subst
              (fromFConstr D) items.toList qedHint with
          | none => none
          | some fid =>
            some { state with db := rest, coreIds := core', nextId := fid }
  | _, _ => none

def execFStepsFuel (fuel : Nat) (state : FBoolCheckState)
    (steps : List VeriPB.ProofStep) : Option FBoolCheckState :=
  match steps with
  | [] => some state
  | step :: rest =>
    let stepResult : Option FBoolCheckState := match step with
      | .formulaSize n =>
        if state.formulaSize != n then none else some state
      | .pol ops =>
        match execFPolRPNBool ops state.db with
        | some result =>
          let newDb := state.db.insert state.nextId
            (normalizeFConstr result)
          some { state with db := newDb, nextId := state.nextId + 1 }
        | none => none
      | .rup constr hints =>
        match VeriPB.opbConstrToPB constr with
        | .ok pbConstr =>
          let fc := toFConstr pbConstr
          if !verifyFRupBool (rupNegateF fc) hints state.db
              state.numVars then none
          else
            let newDb := state.db.insert state.nextId
              (normalizeFConstr fc)
            some { state with db := newDb, nextId := state.nextId + 1 }
        | .error _ => none
      | .pbc constr innerSteps resultId =>
        if innerSteps.any innerStepForbidden then none
        else match fuel with
        | 0 => none
        | n + 1 =>
          match VeriPB.opbConstrToPB constr with
          | .ok pbConstr =>
            let fc := toFConstr pbConstr
            let cs := fc.coeffSum
            if fc.degree > cs then none
            else
              let savedDb := state.db
              let negId := state.nextId
              let dbWithNeg := state.db.insert negId (fc.negateWith cs)
              let subState : FBoolCheckState :=
                { state with db := dbWithNeg, nextId := negId + 1 }
              match execFStepsFuel n subState innerSteps.toList with
              | some finalSub =>
                match finalSub.db[resultId]? with
                | some c =>
                  if !c.isContra then none
                  else
                    let restoredDb := savedDb.insert finalSub.nextId
                      (normalizeFConstr fc)
                    some { state with
                      db := restoredDb
                      nextId := finalSub.nextId + 1 }
                | none => none
              | none => none
          | .error _ => none
      | .ia constr premise =>
        match premise with
        | none => none
        | some pid =>
          match state.db[pid]? with
          | none => none
          | some S =>
            match VeriPB.opbConstrToPB constr with
            | .error _ => none
            | .ok T0 =>
              let T := normalizeFConstr (toFConstr T0)
              if impliesSyntacticF (normalizeFConstr S) T then
                some { state with
                  db := state.db.insert state.nextId T
                  nextId := state.nextId + 1 }
              else none
      | .red constr substPairs goals =>
        match fuel with
        | 0 => none
        | n + 1 =>
          redFStep (execFStepsFuel n) state constr substPairs (goalsToItems goals) none
      | .strengthening rule constr substPairs items qedHint =>
        match rule with
        | .dom => none
        | .red =>
          match fuel with
          | 0 => none
          | n + 1 =>
            redFStep (execFStepsFuel n) state constr substPairs items.toList qedHint
      | .delcChecked ids substPairs sub =>
        match fuel with
        | 0 => none
        | n + 1 => delcCheckedFStep (execFStepsFuel n) state ids substPairs sub
      | .deld ids =>
        if ids.any state.coreIds.contains then none
        else some { state with
          db := ids.foldl (fun db id => db.erase id) state.db
          coreIds := ids.foldl (fun s id => s.erase id) state.coreIds }
      | .delc ids =>
        if state.s2c && !allCoreF state then none
        else some { state with
          db := ids.foldl (fun db id => db.erase id) state.db
          coreIds := ids.foldl (fun s id => s.erase id) state.coreIds }
      | .core ids =>
        if ids.all state.db.contains then
          some { state with coreIds := ids.foldl (fun s id => s.insert id) state.coreIds }
        else none
      | .coreRange lo hi =>
        let core' := state.db.keys.foldl
          (fun s id => if lo ≤ id ∧ id < hi then s.insert id else s) state.coreIds
        some { state with coreIds := core' }
      | .strengtheningToCore on =>
        if on then some { state with coreIds := allIdsF state.db, s2c := true }
        else some { state with s2c := false }
      | .loadOrder (some _) _ => none
      | .loadOrder none _ => some state
      | .defOrder _ => some state
      | .conclusionNone => some state
      | .output => some state
      | .conclusion id =>
        match state.db[id]? with
        | some c => if c.isContra then some state else none
        | none => none
      | .sol lits value =>
        match checkSolutionF state.origConstrs state.objective lits with
        | none => none
        | some b' =>
          if !solValueOk state.offset b' value then none
          else some { state with best := updBest state.best b' }
      | .soli lits value =>
        match checkSolutionF state.origConstrs state.objective lits with
        | none => none
        | some b' =>
          if !solValueOk state.offset b' value then none
          else some { state with
            db := state.db.insert state.nextId
              (toFConstr (improveConstr state.objective b'))
            nextId := state.nextId + 1
            best := updBest state.best b'
            coreIds := state.coreIds.insert state.nextId }
      | .conclusionSat _ => some state
      | .conclusionBounds _ _ _ _ => some state
      | _ => none  -- statements the checker does not support yet
    match stepResult with
    | some s => execFStepsFuel fuel s rest
    | none => none
termination_by (fuel, steps.length)

/-- Runtime mirror of `VeriPB.Reflect.hasUnsatConclusion` (same placement
rule via the shared `lastConclusion`). -/
def hasFUnsatConclusion (steps : Array VeriPB.ProofStep)
    (state : FBoolCheckState) : Bool :=
  state.best.isNone && match lastConclusion steps with
    | some (.conclusion id) => match state.db[id]? with
      | some c => c.isContra
      | none => false
    | _ => false

/-- Runtime implementation of `VeriPB.Reflect.checkProofBool`. -/
def checkProofBoolFast (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (names : List (String × Nat))
    (proofStr : String) : Bool :=
  match VeriPB.parseVeriPBProofWith (VeriPB.VarTable.ofList names numVars)
      proofStr with
  | .error _ => false
  | .ok proofData =>
    let initState := FBoolCheckState.fromConstrs constrs
      (max numVars proofData.numVars) objective
    let stepsList := proofData.steps.toList
    let fuel := pbcDepth stepsList + 1
    match execFStepsFuel fuel initState stepsList with
    | some finalState =>
      hasFUnsatConclusion proofData.steps finalState
    | none => false

/-- Runtime implementation of `VeriPB.Reflect.proofClaim?`: the fast step
loop, then the shared `conclusionClaim` on the final state (database
entries converted back with `fromFConstr`). -/
def proofClaimFast? (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (offset : Int) (names : List (String × Nat))
    (proofStr : String) : Option Claim :=
  match VeriPB.parseVeriPBProofWith (VeriPB.VarTable.ofList names numVars)
      proofStr with
  | .error _ => none
  | .ok proofData =>
    let initState := FBoolCheckState.fromConstrs constrs
      (max numVars proofData.numVars) objective offset
    let stepsList := proofData.steps.toList
    let fuel := pbcDepth stepsList + 1
    match execFStepsFuel fuel initState stepsList with
    | some s =>
      match lastConclusion proofData.steps with
      | some step =>
        conclusionClaim (fun id => (s.db[id]?).map fromFConstr) constrs
          objective offset s.best step
      | none => none
    | none => none

end VeriPB.Reflect.Fast
