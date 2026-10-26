/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import Lean
import Std
import VeriPB.Tactic.Sat.PseudoBoolean
import VeriPB.Tactic.Sat.FromVeriPB
import VeriPB.Tactic.Sat.Dominance

/-!
# Verified VeriPB checker definitions

This module holds the list-based reference checker components shared by the
array-based runtime checker and by the soundness proofs: the proof-checking
state (`BoolCheckState`), pol RPN execution, RUP verification, syntactic
implication, the redundance goals and their coverage tests, solution
checking, the conclusion test, and the pbc depth measure.

The step loop (`processRedItems`, `checkRedundance`, `execStepsFuel`) stays
next to its soundness proofs in `VeriPB.Tactic.Sat.Reflect`, because those
proofs rewrite with hypotheses about the `match` expressions inside it and
Lean's matcher cache is not shared across modules.  The array-based runtime
replacement lives in `VeriPB.Tactic.Sat.ReflectFast`.
-/

namespace VeriPB.Reflect

open Sat.PB

-- Re-export key types
abbrev Constr := Sat.PB.Constr
abbrev Valuation := Sat.PB.Valuation

/-! ## Boolean checker

The checker functions in this module are total and pure (structural or
fuel recursion) to enable formal verification; only the fuel measure
`pbcDepth` is `partial` (it is not part of the soundness proof).
-/

/-- Objective function to minimize: nonnegative coefficients over literals,
as the OPB `min:` line after normalization. The constant offset of the OPB
objective (`VeriPB.OPBObjective.offset`) is kept apart (`BoolCheckState.offset`):
the OPB value of a valuation is `objVal obj v + offset` (`opbVal`).
A decision instance has the empty objective `[]`. -/
abbrev Objective := List Sat.PB.Term

/-- Objective value of a valuation. -/
def objVal (obj : Objective) (v : Valuation) : Nat := Sat.PB.evalSum v obj

/-- OPB objective value of a valuation: `objVal obj v + offset`. -/
def opbVal (obj : Objective) (offset : Int) (v : Valuation) : Int :=
  (objVal obj v : Int) + offset

/-- Check state for the Boolean checker. Uses arrays for efficiency. -/
structure BoolCheckState where
  /-- Constraint database: maps ID to constraint -/
  db : Std.HashMap Nat Constr
  /-- Original formula constraints (for solution checking); never changes
  during execution -/
  origConstrs : Array Constr
  /-- Original objective function (`[]` for decision instances); never
  changes. The theorems are about `opbVal objective offset`. -/
  objective : Objective
  /-- Constant offset of the original OPB objective; never changes. -/
  offset : Int := 0
  /-- Current objective (VeriPB's objective after `obju` updates; initially
  `objective`). Used by solution logging, the `red` objective goal and the
  lower bound of `conclusion BOUNDS`. -/
  curObj : Objective
  /-- Constant offset of the current objective. -/
  curOffset : Int := 0
  /-- Lower-bound threshold in OPB units (CakePB `dbound`, VeriPB
  `best_objective_value`): the minimum of the values of `sol`, `soli` and
  `obji`; `none` before any. The invariant `DBOpt` is about the solutions
  below it. -/
  best : Option Int
  /-- Best witnessed OPB value (CakePB `bound`): the minimum original
  objective value of the solutions logged by `sol`/`soli` while checked
  deletion was on (`chk`); `none` before any. Upper bounds and
  `conclusion SAT` without a solution rest on it. -/
  bestWit : Option Int
  /-- Checked deletion still on (CakePB `chk`): false after a plain
  `delc`. Gates the `bestWit` updates (parity); no soundness proof uses
  it. -/
  chk : Bool := true
  /-- The instance has an objective (VeriPB/CakePB `objective present`):
  `obji`, `eobj` and `obju` need one. An objective
  without terms counts as absent (the checker sees `[]` either way).
  Parity only; no soundness proof uses it. -/
  hasObj : Bool := true
  /-- Inside a core-only subproof (checked `delc`, `obju`): every constraint
  of the database counts as core, so `deld` is rejected (VeriPB adds the
  subproof's derivations to the core, CakePB `insert_fml T`). Parity only;
  no soundness proof uses it. -/
  coreOnly : Bool := false
  /-- Next available constraint ID -/
  nextId : Nat
  /-- Number of variables -/
  numVars : Nat
  /-- Expected formula size -/
  formulaSize : Nat
  /-- Ids of the core constraints (VeriPB's core set). It decides the
  `deld`/`delc` preconditions, which constraints a checked deletion and
  `obju` see (goals, hints), and, under `strengthening_to_core`, which
  constraints get `red` database goals. Soundness-relevant through the
  invariant clauses `CoreImplied` (while `s2c` is on, the core implies every
  database constraint) and `OrdInv` (while an order is loaded, every core
  model has a database model below it in the order). -/
  coreIds : Std.HashSet Nat := {}
  /-- `strengthening_to_core` mode: new `red` results go to the core and
  `red` database goals range over the core only. -/
  s2c : Bool := false
  /-- The orders defined by `def_order`, newest first (a lookup finds the
  last definition of a name, as VeriPB and CakePB). Each one passed its
  spec, transitivity and reflexivity checks (invariant clause
  `StoredGood`). -/
  orders : List (String × Sat.PB.Dominance.OrderData) := []
  /-- The loaded order with its literals, by value (a later `def_order` of
  the same name does not change it); `none` when no order is loaded. -/
  ord : Option (Sat.PB.Dominance.OrderData × List Sat.PB.Literal) := none
  deriving Inhabited

/-- Build HashMap from list with starting index (pure recursive). -/
def mkDBRec : List Constr → Nat → Std.HashMap Nat Constr
  | [], _ => {}
  | c :: rest, i => (mkDBRec rest (i + 1)).insert i c

/-- Initialize check state from an array of constraints and an objective. -/
def BoolCheckState.fromConstrs (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (offset : Int := 0) : BoolCheckState :=
  { db := mkDBRec (constrs.toList.map VeriPB.normalizeConstr) 1
    origConstrs := constrs
    objective := objective
    offset := offset
    curObj := objective
    curOffset := offset
    best := none
    bestWit := none
    chk := true
    hasObj := !objective.isEmpty
    coreOnly := false
    nextId := constrs.size + 1
    numVars := numVars
    formulaSize := constrs.size
    coreIds := (List.range constrs.size).foldl (fun s i => s.insert (i + 1)) {}
    s2c := false
    orders := []
    ord := none }

/-- The set of all ids of a database (`strengthening_to_core on`). -/
def allIds (db : Std.HashMap Nat Constr) : Std.HashSet Nat :=
  db.keys.foldl (fun s id => s.insert id) {}

/-- Every constraint of the database is core. -/
def allCore (s : BoolCheckState) : Bool :=
  s.db.keys.all fun id => s.coreIds.contains id

/-! ### Pol RPN execution (pure recursive) -/

/-- Execute a single pol operation on the stack. -/
def execPolOne (db : Std.HashMap Nat Constr) (stack : List VeriPB.StackElem)
    (op : VeriPB.PolOp) : Option (List VeriPB.StackElem) :=
  match op with
  | .pushId id => match db[id]? with
    | some c => some (.constr c :: stack)
    | none => none
  | .pushNat n => some (.nat n :: stack)
  | .pushLitAxiom lit => match VeriPB.opbLitToPB lit with
    | .ok pbLit => some (.constr ⟨[(1, pbLit)], 0⟩ :: stack)
    | .error _ => none
  | .add => match stack with
    | .constr c2 :: .constr c1 :: rest =>
      some (.constr (VeriPB.addConstrs c1 c2) :: rest)
    | _ => none
  | .mul => match stack with
    | .nat k :: .constr c :: rest =>
      some (.constr (VeriPB.mulConstr c k) :: rest)
    | _ => none
  | .div => match stack with
    | .nat k :: .constr c :: rest =>
      if k == 0 then none
      else some (.constr (VeriPB.divConstr (VeriPB.normalizeConstr c) k) :: rest)
    | _ => none
  | .saturate => match stack with
    | .constr c :: rest =>
      some (.constr (VeriPB.saturateConstr (VeriPB.normalizeConstr c)) :: rest)
    | _ => none
  | .weaken varName => match stack with
    | .constr c :: rest =>
      if varName.startsWith "x" then
        match (varName.drop 1).toString.toNat? with
        | some n => if n > 0 then
            -- VeriPB weakens the normalized constraint
            some (.constr (VeriPB.weakenConstr (VeriPB.normalizeConstr c) (n - 1)) :: rest)
          else none
        | none => none
      else none
    | _ => none
  | .lowerRhs => match stack with
    | .nat k :: .constr c :: rest =>
      -- `k -`: lower the degree of the normalized constraint by `k`
      -- (Nat subtraction: a weaker constraint, so always sound)
      let nc := VeriPB.normalizeConstr c
      some (.constr ⟨nc.terms, nc.degree - k⟩ :: rest)
    | _ => none
  | .divVar => match stack with
    | .nat k :: .constr c :: rest =>
      -- `k c`: variable-form division of the normalized constraint
      if k == 0 then none
      else some (.constr (Sat.PB.cgDivConstr (VeriPB.normalizeConstr c) k) :: rest)
    | _ => none
  | .mir => match stack with
    | .nat k :: .constr c :: rest =>
      -- `k n`: normalized MIR cut of the normalized constraint
      if k == 0 then none
      else some (.constr (Sat.PB.mirConstr (VeriPB.normalizeConstr c) k) :: rest)
    | _ => none
  | .mirVar => match stack with
    | .nat k :: .constr c :: rest =>
      -- `k m`: variable-form MIR cut of the normalized constraint
      if k == 0 then none
      else some (.constr (Sat.PB.mirVarConstr (VeriPB.normalizeConstr c) k) :: rest)
    | _ => none

/-- Execute pol RPN operations on a stack. Pure recursive. -/
def execPolOps (db : Std.HashMap Nat Constr) :
    List VeriPB.PolOp → List VeriPB.StackElem → Option (List VeriPB.StackElem)
  | [], stack => some stack
  | op :: rest, stack =>
    match execPolOne db stack op with
    | some s => execPolOps db rest s
    | none => none

/-- Execute pol RPN and return result constraint (or none on error). -/
def execPolRPNBool (ops : List VeriPB.PolOp) (db : Std.HashMap Nat Constr) :
    Option Constr :=
  match execPolOps db ops [] with
  | some [.constr c] => some c
  | _ => none

/-! ### RUP verification by unit propagation

`rup C : hints` is accepted iff ONE pass of PB unit propagation over the
hint constraints, in the given order and starting from the empty
assignment, reaches a conflict. This is CakePB's `check_rup`
(npbc_checkScript.sml:404): forced literals are applied as they come, the
step succeeds at the first conflicting hint, the negated target takes part
only where the hint list names it with `~` (any position, any number of
times), and an empty hint list is rejected (one pass over no constraints
never conflicts). VeriPB repeats rounds to a fixpoint and propagates the
negated target implicitly, so it accepts more; its elaborated output lists
the hints in propagation order and carries `~` where the negated target
propagates, so it replays in one pass.

The definitions below are pure and structurally recursive; their soundness
(`propagateRound_sound` and `verifyRupBool_implied` in `Reflect.lean`) says
that a valuation satisfying every hint constraint extends every assignment
the propagation builds, so a conflict refutes all such valuations.

Propagation of a constraint `Σ a_l l ≥ d` under a partial assignment: the
slack is `Σ_{l not falsified} a_l − d`; a negative slack is a conflict, and
every unassigned literal with `a_l > slack` is forced true. -/

/-- Partial assignment indexed by variable: `some b` is assigned, `none`
(and every index outside the array) is unassigned. -/
abbrev PAsgn := Array (Option Bool)

/-- Value of variable `i` (total: out of range is unassigned). -/
def PAsgn.get (a : PAsgn) (i : Nat) : Option Bool := a[i]?.getD none

/-- Value of a literal under a partial assignment. -/
def litValP (a : PAsgn) : Sat.PB.Literal → Option Bool
  | .pos i => a.get i
  | .neg i => (a.get i).map (!·)

/-- The variable value that makes a literal true. -/
def litPol : Sat.PB.Literal → Bool
  | .pos _ => true
  | .neg _ => false

/-- Make literal `l` true (a no-op when its variable is out of range). -/
def PAsgn.setLit (a : PAsgn) (l : Sat.PB.Literal) : PAsgn :=
  a.set! l.var (some (litPol l))

/-- Sum of the coefficients of the terms whose literal is not falsified. -/
def activeSum (a : PAsgn) : List Sat.PB.Term → Nat
  | [] => 0
  | (c, l) :: rest =>
    (if litValP a l = some false then 0 else c) + activeSum a rest

/-- Unassigned literals with coefficient above the slack, in term order. -/
def forcedLits (a : PAsgn) (slack : Nat) : List Sat.PB.Term → List Sat.PB.Literal
  | [] => []
  | (c, l) :: rest =>
    if slack < c ∧ litValP a l = none then l :: forcedLits a slack rest
    else forcedLits a slack rest

/-- Outcome of propagating one constraint. -/
inductive PropOutcome where
  | conflict
  | forced (lits : List Sat.PB.Literal)
  | nothing

/-- Propagate one constraint under `a`. -/
def propagateConstr (a : PAsgn) (c : Constr) : PropOutcome :=
  let act := activeSum a c.terms
  if act < c.degree then .conflict
  else match forcedLits a (act - c.degree) c.terms with
    | [] => .nothing
    | ls => .forced ls

/-- Make the forced literals true in order; `none` (conflict) when one of
them is already false (it was unassigned when it was forced, so an earlier
literal of the same list set its variable the other way). -/
def assignLits (a : PAsgn) : List Sat.PB.Literal → Option PAsgn
  | [] => some a
  | l :: ls => match litValP a l with
    | some true => assignLits a ls
    | some false => none
    | none => assignLits (a.setLit l) ls

/-- One propagation pass over the hint constraints in order, applying
forced literals as they come. `none` is a conflict; otherwise the new
assignment and whether some constraint forced a literal. -/
def propagateRound (a : PAsgn) (changed : Bool) :
    List Constr → Option (PAsgn × Bool)
  | [] => some (a, changed)
  | c :: cs => match propagateConstr a c with
    | .conflict => none
    | .nothing => propagateRound a changed cs
    | .forced ls => match assignLits a ls with
      | none => none
      | some a' => propagateRound a' true cs

/-- `1 +` the largest variable index of the constraints (`0` if none). -/
def varBound (hs : List Constr) : Nat :=
  hs.foldl (fun m c => c.terms.foldl (fun m t => max m (t.2.var + 1)) m) 0

/-- Resolve a RUP hint to a constraint. -/
def resolveHint (negConstr : Constr) (db : Std.HashMap Nat Constr)
    (h : VeriPB.RupHint) : Option Constr :=
  match h with
  | .negC => some negConstr
  | .id n => db[n]?

/-- Resolve all hints (`none` if an id is not in the database). All ids are
resolved before propagation, so a missing id after the conflicting hint
rejects the step (CakePB never looks it up and accepts). -/
def resolveHints (negConstr : Constr) (db : Std.HashMap Nat Constr) :
    List VeriPB.RupHint → Option (List Constr)
  | [] => some []
  | h :: hs => match resolveHint negConstr db h, resolveHints negConstr db hs with
    | some c, some cs => some (c :: cs)
    | _, _ => none

/-- Negation of a `rup` target, as VeriPB propagates over it: the target is
normalized first (so complementary pairs and repeated literals do not
weaken propagation); a target whose degree exceeds its coefficient sum is
unsatisfiable on its own, and its negation is trivially true: the negated
terms with degree `0` (as `negTriv`; CakePB's `not` keeps the terms with a
non-positive degree). -/
def rupNegate (c : Constr) : Constr :=
  let nc := VeriPB.normalizeConstr c
  if nc.degree ≤ nc.coeffSum then nc.negate else ⟨nc.negate.terms, 0⟩

/-- Verify a RUP step: one propagation pass over the resolved hint
constraints (`~` resolves to `negConstr`), from the empty assignment,
reaches a conflict. The assignment covers `varBound hs` variables, so every
literal of the hints is in range. `numVars` is unused. -/
def verifyRupBool (negConstr : Constr) (hints : List VeriPB.RupHint)
    (db : Std.HashMap Nat Constr) (_numVars : Nat) : Bool :=
  match resolveHints negConstr db hints with
  | none => false
  | some hs =>
    (propagateRound (Array.replicate (varBound hs) none) false hs).isNone

/-! ### Constraint matching (redundance goals) -/

/-- Check if two normalized constraints match (same degree and sorted terms). -/
def constrMatchNorm (c1 c2 : Constr) : Bool :=
  c1.degree == c2.degree && c1.terms.length == c2.terms.length &&
  -- Compare sorted term lists
  let sort := fun (ts : List (Nat × Sat.PB.Literal)) =>
    ts.mergeSort fun a b =>
      Sat.PB.Literal.var a.2 < Sat.PB.Literal.var b.2 ||
      (Sat.PB.Literal.var a.2 == Sat.PB.Literal.var b.2 &&
       match a.2, b.2 with
       | .pos _, .neg _ => true
       | _, _ => false)
  sort c1.terms == sort c2.terms

/-- Check if a constraint (after normalization) is in the database. -/
def constrInDB (c : Constr) (db : Std.HashMap Nat Constr) : Bool :=
  let nc := VeriPB.normalizeConstr c
  db.toList.any fun (_, dbC) => constrMatchNorm nc (VeriPB.normalizeConstr dbC)

/-! ### Syntactic implication

VeriPB's and CakePB's implication check (MEM_039 §1), used by `ia` and to
discharge redundance goals. For a source `S = Σ s_l l ≥ A` and a target
`T = Σ t_l l ≥ B`: `S` implies `T` if `B = 0`, or `S` is contradictory, or
`B + Σ_{l ∈ S} cost(l) ≤ A`, where `cost(l) = s_l` if `l` does not occur
in `T` (weakened away) and `s_l - t_l` if it occurs with `t_l < s_l` and
`t_l < B` (the excess, free by saturation), else `0`. The literals of `S`
must be pairwise distinct (true for normalized constraints; checked, since
a repeated literal would make the cost count a target coefficient twice). -/

/-- Coefficient of the first occurrence of literal `l` in a term list. -/
def coeffOf (l : Sat.PB.Literal) : List Sat.PB.Term → Option Nat
  | [] => none
  | (a, l') :: rest => if l' == l then some a else coeffOf l rest

/-- Weakening cost of the source term `s·l` against the target terms `T`
with degree `B`. -/
def impCost (T : List Sat.PB.Term) (B s : Nat) (l : Sat.PB.Literal) : Nat :=
  match coeffOf l T with
  | none => s
  | some t => if t < s ∧ t < B then s - t else 0

/-- Total weakening cost of the source terms. -/
def impCostSum (T : List Sat.PB.Term) (B : Nat) : List Sat.PB.Term → Nat
  | [] => 0
  | (s, l) :: rest => impCost T B s l + impCostSum T B rest

/-- The literals of a constraint are pairwise distinct. -/
def litsNodup (c : Constr) : Bool := decide (c.terms.map Prod.snd).Nodup

/-- Syntactic implication `S ⊢ T` (VeriPB `implies`, CakePB `imp`). -/
def impliesSyntactic (S T : Constr) : Bool :=
  T.degree == 0 || decide (S.coeffSum < S.degree) ||
    (litsNodup S && decide (T.degree + impCostSum T.terms T.degree S.terms ≤ S.degree))

/-- Negation of a normalized constraint for insertion into a subproof: the
negation if the constraint is satisfiable by its coefficients, else the
negated terms with degree `0` (CakePB's `not`, whose degree is non-positive
there; every degree-0 constraint is satisfied). -/
def negTriv (c : Constr) : Constr :=
  if c.degree ≤ c.coeffSum then c.negate else ⟨c.negate.terms, 0⟩

/-- A goal that holds for every valuation because it contains a
complementary pair `a·l`, `b·¬l` with `min a b ≥ degree` (one of the two
literals is true). CakePB's `subst_opt` cancels such a pair and gets a
non-positive degree; the normalizer keeps the pair when `min a b` exceeds
the degree. -/
def trivialByPair (G : Constr) : Bool :=
  G.terms.any fun t => G.terms.any fun u =>
    decide (u.2 = t.2.negate) && decide (G.degree ≤ min t.1 u.1)

/-! ### Redundance goals (`red`, checked `delc`)

The goals of a redundance step `C : ω` follow CakePB `check_red`
(MEM_039 §2): `#1` is `C|ω`, `#2` the objective goal `f - f|ω ≥ 0` (when
there is an objective), and every database constraint `D` touched by `ω`
gives a goal `D|ω`. All goal constraints are normalized. -/

/-- Literal `l` is untouched by the witness or mapped to a constant that
satisfies it. -/
def litSetTrue (subst : List (Nat × Sat.PB.SubstVal)) (l : Sat.PB.Literal) : Bool :=
  match Sat.PB.lookupSubst subst l.var with
  | none => true
  | some .one => match l with
    | .pos _ => true
    | .neg _ => false
  | some .zero => match l with
    | .pos _ => false
    | .neg _ => true
  | some _ => false

/-- Every literal the witness touches is set to true (CakePB `subst_opt`
`same`): then `ω` can only raise the left-hand side, and no goal is needed. -/
def touchedSatisfied (subst : List (Nat × Sat.PB.SubstVal))
    (ts : List Sat.PB.Term) : Bool :=
  ts.all fun t => litSetTrue subst t.2

/-- Normalized goal constraint `D|ω`. -/
def substGoal (subst : List (Nat × Sat.PB.SubstVal)) (D : Constr) : Constr :=
  VeriPB.normalizeConstr (Sat.PB.applySubstConstr subst D)

/-- Objective goal `f - f|ω ≥ 0` as a Nat constraint:
`Σ a l + Σ a ¬(l|ω) ≥ Σ a`, with constant substitutions folded into the
degree, normalized. A valuation satisfying it is not improved upon by
applying the witness. -/
def objGoalConstr (subst : List (Nat × Sat.PB.SubstVal)) (obj : Objective) : Constr :=
  let s := Sat.PB.applySubstConstr subst
    ⟨obj.map (fun (a, l) => (a, l.negate)), Sat.PB.coeffSumR obj⟩
  VeriPB.normalizeConstr ⟨obj ++ s.terms, s.degree⟩

/-- Goal constraint of a `proofgoal` id: `#1` is `C|ω`, `#2` the objective
goal (only with an objective), a number `n` is `D|ω` for the constraint `n`
of `goalDb` (the database before the step; core only for checked
deletion and, under `strengthening_to_core`, for `red`). Other ids are
invalid. -/
def redGoalOf (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (obj : Objective) (goalDb : Std.HashMap Nat Constr) (gid : String) :
    Option Constr :=
  if gid == "#1" then some (substGoal subst C)
  else if gid == "#2" then
    if obj.isEmpty then none else some (objGoalConstr subst obj)
  else if gid.startsWith "#" then none
  else match gid.toNat? with
    | some n => (goalDb[n]?).map (substGoal subst)
    | none => none

/-- The `#` goals are discharged: `#1` when trivially true by a
complementary pair (`trivialByPair`), by a subproof or by implication from
`¬C`; the objective goal (only when `ω` touches the objective) the
same way (CakePB `check_hash_goals`). A proved `#k` is recognized by its id
and its constraint (identical by construction; matching the constraint
keeps the soundness proof free of reasoning about goal ids). -/
def hashGoalsCovered (subst : List (Nat × Sat.PB.SubstVal)) (C nC : Constr)
    (obj : Objective) (proved : List (String × Constr)) : Bool :=
  (let G1 := substGoal subst C
   trivialByPair G1 ||
   proved.any (fun p => p.1 == "#1" && constrMatchNorm G1 p.2) ||
     impliesSyntactic nC G1) &&
  (!Sat.PB.termsAffected subst obj ||
    (let G2 := objGoalConstr subst obj
     trivialByPair G2 ||
     proved.any (fun p => p.1 == "#2" && constrMatchNorm G2 p.2) ||
       impliesSyntactic nC G2))

/-- The database goal of a constraint `D` needs no subproof or has one
(CakePB `subst_opt` and `split_goals`): `ω` sets every touched literal of
`D` true, or `D|ω` is trivially true by a complementary pair
(`trivialByPair`), or `D` implies `D|ω` (includes `D|ω` with degree 0), or
`¬C` implies
`D|ω`, or `D|ω` equals a database goal proved by a `proofgoal` (its own
goal included: CakePB checks that one by id, the constraints are identical)
or a constraint of `lookupDb` (the database before the step: all of it for
`red`, the core for checked deletion). -/
def dbGoalCovered (subst : List (Nat × Sat.PB.SubstVal)) (nC : Constr)
    (lookupDb : Std.HashMap Nat Constr) (proved : List (String × Constr))
    (D : Constr) : Bool :=
  touchedSatisfied subst D.terms ||
    (let G := substGoal subst D
     trivialByPair G ||
     impliesSyntactic (VeriPB.normalizeConstr D) G ||
     impliesSyntactic nC G ||
     proved.any (fun p => !p.1.startsWith "#" && constrMatchNorm G p.2) ||
     constrInDB G lookupDb)

/-- Steps allowed inside subproofs (`pbc`, `proofgoal`, the top level of a
`red` or checked-deletion subproof): CakePB's `lstep`s. All of them derive
implied constraints or delete. -/
def isLStep : VeriPB.ProofStep → Bool
  | .pol _ | .rup _ _ | .ia _ _ | .pbc _ _ _ | .deld _ => true
  | _ => false

/-- The old `red` constructor's goals as subproof items. -/
def goalsToItems (goals : Array (String × Array VeriPB.ProofStep × Nat)) :
    List VeriPB.ProofStep :=
  goals.toList.map fun (g, steps, h) => .proofgoal g steps (some h)

/-! ### Solution logging -/

/-- Solution-logging steps (`sol`, `soli`). -/
def isSolStep : VeriPB.ProofStep → Bool
  | .sol _ _ | .soli _ _ => true
  | _ => false

/-- Steps rejected inside a subproof: everything but the `lstep`s
(`isLStep`). In particular solution logging, conclusions and `red`. -/
def innerStepForbidden (s : VeriPB.ProofStep) : Bool := !isLStep s

/-- Total valuation of a logged solution: a variable is true iff its
positive literal is listed (unlisted variables are false). -/
def solValuation (lits : List Sat.PB.Literal) : Valuation :=
  fun i => lits.contains (.pos i)

/-- Boolean evaluation of a constraint. -/
def constrSatB (c : Constr) (v : Valuation) : Bool :=
  decide (c.degree ≤ Sat.PB.evalSum v c.terms)

/-- Boolean evaluation of a formula (every constraint satisfied). -/
def formulaSatB (F : Array Constr) (v : Valuation) : Bool :=
  F.toList.all fun c => constrSatB c v

/-- Check a logged solution against the original formula and return its
objective value. The literal list is read as a total valuation
(`solValuation`); it must satisfy every original constraint. This is
stricter than VeriPB, which checks against the core set. -/
def checkSolution (F : Array Constr) (obj : Objective)
    (lits : List VeriPB.OPBLit) : Option Nat :=
  match lits.mapM VeriPB.opbLitToPB with
  | .error _ => none
  | .ok pl =>
    let ρ := solValuation pl
    if formulaSatB F ρ then some (objVal obj ρ) else none

/-- `checkSolution` returning the values of the solution under the original
objective `obj` and the current objective `curObj` (in that order). -/
def checkSolutionVals (F : Array Constr) (obj curObj : Objective)
    (lits : List VeriPB.OPBLit) : Option (Nat × Nat) :=
  match lits.mapM VeriPB.opbLitToPB with
  | .error _ => none
  | .ok pl =>
    let ρ := solValuation pl
    if formulaSatB F ρ then some (objVal obj ρ, objVal curObj ρ) else none

/-- The value written after a logged solution (`sol`/`soli lits : v`) must
equal the OPB value of the solution under the current objective,
`b' + offset` where `b'` is its `objVal` (VeriPB `SolutionIncorrectValue`,
CakePB likewise; MEM_039 §7). No value written: nothing to check. On an
instance without objective the value must be 0 (CakePB; VeriPB rejects
any value there, `SolutionValueHintNoObjective`). -/
def solValueOk (offset : Int) (b' : Nat) (value : Option Int) : Bool :=
  match value with
  | none => true
  | some v => (b' : Int) + offset == v

/-- Best value after logging the value `b'`. -/
def updBest (best : Option Int) (b' : Int) : Option Int :=
  match best with
  | none => some b'
  | some b => some (min b b')

/-- Witnessed value after logging a solution of original value `b'`: lowered
only while checked deletion is on (`chk`; CakePB `bound`, VeriPB
`best_valid_objective_value`). After a plain `delc` the references no
longer count logged solutions as witnesses, so neither does the checker
(the update would be sound, the solution is checked against the original
formula; this keeps parity). -/
def updBestWit (chk : Bool) (bestWit : Option Int) (b' : Int) : Option Int :=
  if chk then updBest bestWit b' else bestWit

/-- Objective-improvement constraint added by `soli` for a solution of value
`b'`: the negation of `obj ≥ b'`, i.e. `Σ aᵢ¬lᵢ ≥ coeffSum − b' + 1`, which
says `obj ≤ b' − 1` (contradictory when `b' = 0`). Meaningful only for
`b' ≤ coeffSum`, which holds because `b'` is an objective value (for larger
`b'` the Nat degree is 1, not 0; `objiConstr` handles that range). -/
def improveConstr (obj : Objective) (b' : Nat) : Constr :=
  Constr.negate ⟨obj, b'⟩

/-- Constraint added by `obji v` (VeriPB `solution_logging.rs:215-231`,
CakePB `model_improving`): `Σ aᵢ¬lᵢ ≥ coeffSum + 1 + offset − v`, which says
`obj + offset ≤ v − 1` over the current objective (contradictory for a value
below the offset, trivial for a value above the maximum; a negative degree
is truncated to 0 as everywhere in the checker). Equals
`improveConstr obj (v − offset)` for `0 ≤ v − offset ≤ coeffSum`. -/
def objiConstr (obj : Objective) (offset v : Int) : Constr :=
  ⟨obj.map fun (a, l) => (a, l.negate),
    ((Sat.PB.coeffSumR obj : Int) + 1 + offset - v).toNat⟩

/-! ### Objective statements (`obju`, `eobj`)

Semantics: testcampaign/p2b/semantics.md §2.2-2.3 (VeriPB `objective_update.rs`,
`equal_objective.rs`; CakePB `check_change_obj`, `eq_obj`). -/

/-- A proof objective (`obju`, `eobj`: integer coefficients plus a constant)
as nonnegative terms plus the constant, as the OPB parser reads an
objective: `-a·l` becomes `a·¬l` with `-a` added to the constant. -/
def proofObjToPB (pobj : VeriPB.ProofObjective) :
    Except String (Objective × Int) := do
  let ts ← pobj.terms.mapM fun (c, l) => do
    let pl ← VeriPB.opbLitToPB l
    pure (c, pl)
  let (terms, adj) := ts.foldl (init := (([] : List Sat.PB.Term), (0 : Int)))
    fun (acc, adj) (c, l) =>
      if c ≥ 0 then ((c.toNat, l) :: acc, adj)
      else (((-c).toNat, l.negate) :: acc, adj + c)
  pure (terms.reverse, pobj.constant + adj)

/-- Canonical form of an objective with constant: the signed coefficient of
each variable (`a·¬x` is `−a·x + a`), merged, zeros dropped, sorted by
variable. Two objectives are equal as functions iff their canonical forms
agree (VeriPB's `PBObjective` normal form; CakePB's `eq_obj`). Parity only
(`eobj`, `obju`): no soundness proof depends on it. -/
def canonObj (obj : Objective) (c : Int) : List (Nat × Int) × Int :=
  let signed : List (Nat × Int) := obj.map fun (a, l) => match l with
    | .pos x => (x, (a : Int))
    | .neg x => (x, -(a : Int))
  let c' := obj.foldl (fun acc (a, l) => match l with
    | .pos _ => acc
    | .neg _ => acc + (a : Int)) c
  let sorted := signed.mergeSort fun p q => decide (p.1 ≤ q.1)
  let merged := sorted.foldr (fun (x, a) acc => match acc with
    | (y, b) :: rest => if x == y then (y, a + b) :: rest else (x, a) :: acc
    | [] => [(x, a)]) []
  (merged.filter fun p => p.2 != 0, c')

/-- The canonical form back as nonnegative terms plus constant: `−a·x`
becomes `a·¬x` with `−a` added to the constant. The result is the merged,
variable-sorted objective VeriPB keeps (`PBObjective::from_terms`). -/
def normalizeObjective (obj : Objective) (c : Int) : Objective × Int :=
  let (m, c') := canonObj obj c
  (m.map fun (x, a) => if a ≥ 0 then (a.toNat, Literal.pos x)
      else ((-a).toNat, Literal.neg x),
   m.foldl (fun acc (_, a) => if a ≥ 0 then acc else acc + a) c')

/-- The objective after `obju`: `new` replaces it, `diff` adds the terms and
the constant; both merged (`normalizeObjective`), as VeriPB and CakePB keep
their objective (later `soli`/`obji` constraints are built from it). -/
def objuNew (kind : VeriPB.ObjUpdateKind) (curObj : Objective)
    (curOffset : Int) (terms : Objective) (constant : Int) :
    Objective × Int :=
  match kind with
  | .new => normalizeObjective terms constant
  | .diff => normalizeObjective (curObj ++ terms) (curOffset + constant)

/-- `f + c ≥ g + d` as a Nat constraint:
`Σ f + Σ aᵢ¬lᵢ (over g) ≥ coeffSum g + d − c` (a negative degree is
truncated to 0, the constraint is then trivially true, as is the
inequality). The `obju` goals: `#1` is `f_new + c_new ≥ f_old + c_old`,
`#2` the converse (VeriPB `objective_update.rs:87-146`; in `diff` mode the
same constraints after normalization, `d ≥ 0` and `−d ≥ 0`). -/
def objGeqConstr (f : Objective) (c : Int) (g : Objective) (d : Int) :
    Constr :=
  ⟨f ++ g.map (fun (a, l) => (a, l.negate)),
    ((Sat.PB.coeffSumR g : Int) + d - c).toNat⟩

/-- Goal lookup of an `obju` subproof: `#1`, `#2` only. -/
def objuGoalOf (G1 G2 : Constr) (gid : String) : Option Constr :=
  if gid == "#1" then some G1 else if gid == "#2" then some G2 else none

/-- An `obju` goal is covered when it is trivial (normalized degree 0, or
true by a complementary pair `trivialByPair`: together CakePB's
`check_trivial`, whose normalization cancels such pairs) or proved by a
`proofgoal` block with its id (identical constraint by construction,
matched by `constrMatchNorm`). -/
def objuGoalCovered (gid : String) (G : Constr)
    (proved : List (String × Constr)) : Bool :=
  G.degree == 0 || trivialByPair G ||
    proved.any fun p => p.1 == gid && constrMatchNorm G p.2

/-- `eobj f`: the instance has an objective and `f` equals the current
objective as a function. No state change. -/
def eobjOk (hasObj : Bool) (curObj : Objective) (curOffset : Int)
    (pobj : VeriPB.ProofObjective) : Bool :=
  hasObj && match proofObjToPB pobj with
    | .error _ => false
    | .ok (ts, c) => canonObj ts c == canonObj curObj curOffset

/-- Conclusion steps (`conclusion NONE` included). -/
def isConclusionStep : VeriPB.ProofStep → Bool
  | .conclusion _ | .conclusionSat _ | .conclusionBounds _ _ _ _
  | .conclusionNone => true
  | _ => false

/-- Output steps (`output NONE` and the output claims). -/
def isOutputStep : VeriPB.ProofStep → Bool
  | .output | .outputClaim _ _ => true
  | _ => false


/-! ### Conclusions: UNSAT, SAT, BOUNDS

The acceptance rules follow CakePB's `check_hconcl` (npbc_checkScript.sml)
and VeriPB's `conclusion.rs` where the two agree; see MEM_039 §6 and the
P2a report for the citations and deviations. A conclusion is evaluated on
the final state of the step loop. -/

/-- What a proof's conclusion certifies; `VeriPB.Reflect.Claim.holds` gives
the meaning. Bounds refer to the normalized objective in minimization form,
`objVal objective v + offset`; for `max: f` the parser negates the objective,
so the bounds are on `−f`. `none` stands for `INF`. -/
inductive Claim where
  | unsat
  | sat
  | bounds (lb ub : Option Int)
  deriving DecidableEq, Repr, Inhabited

/-- A `conclusion BOUNDS` bound as an `Option Int` (`INF` is `none`). -/
def boundOpt : VeriPB.Bound → Option Int
  | .finite v => some v
  | .inf => none

/-- Lower-bound target `objective ≥ lb − offset` (the degree truncated at 0:
a target with degree `≤ 0` is trivial). -/
def lowerBoundConstr (obj : Objective) (offset lb : Int) : Constr :=
  ⟨obj, (lb - offset).toNat⟩

/-- Lower bound `lb : id` of `conclusion BOUNDS` (CakePB `check_hconcl`
`HOBounds`): the hint id is required and must be in the database. `INF`
(`none`): no logged value (`best = none`) and a contradictory constraint
`id`. A finite `lb`: at most the threshold (`lb ≤ best`, CakePB
`opt_le lbi dbound`), and constraint `id` syntactically implies
`curObj ≥ lb − curOffset` over the current objective (`impliesSyntactic`;
a contradictory constraint implies everything). -/
def lowerBoundOk (getC : Nat → Option Constr) (curObj : Objective)
    (curOffset : Int) (best : Option Int) (lb : Option Int)
    (hint : Option Nat) : Bool :=
  match hint with
  | none => false
  | some id =>
    match getC id with
    | none => false
    | some D =>
      match lb with
      | none => best.isNone && D.isContra
      | some l =>
        (match best with
          | none => true
          | some b => decide (l ≤ b)) &&
        impliesSyntactic (VeriPB.normalizeConstr D)
          (VeriPB.normalizeConstr (lowerBoundConstr curObj curOffset l))

/-- Upper bound `ub [: lits]` of `conclusion BOUNDS` (CakePB): `INF` needs
nothing; a finite `ub` needs a solution of original OPB value at most
`ub`: the solution `lits` checked against the original formula, or without
`lits` the best witnessed value `bestWit` (CakePB `bound`). -/
def upperBoundOk (F : Array Constr) (obj : Objective) (offset : Int)
    (bestWit : Option Int) (ub : Option Int)
    (lits : Option (List VeriPB.OPBLit)) : Bool :=
  match ub with
  | none => true
  | some u =>
    match lits with
    | none => match bestWit with
      | none => false
      | some b => decide (b ≤ u)
    | some ls => match checkSolution F obj ls with
      | none => false
      | some val => decide ((val : Int) + offset ≤ u)

/-- `conclusion SAT [: lits]` (CakePB `HDSat`): with `lits`, a solution of
the original formula; without, some logged solution (`bestWit`). -/
def satOk (F : Array Constr) (obj : Objective) (bestWit : Option Int)
    (lits : Option (List VeriPB.OPBLit)) : Bool :=
  match lits with
  | none => bestWit.isSome
  | some ls => (checkSolution F obj ls).isSome

/-- The objective-related part of a final state, as the conclusion check
reads it (shared by the verified and the fast checker). -/
structure ConclCtx where
  objective : Objective
  offset : Int
  curObj : Objective
  curOffset : Int
  best : Option Int
  bestWit : Option Int
  chk : Bool

def BoolCheckState.conclCtx (s : BoolCheckState) : ConclCtx :=
  { objective := s.objective, offset := s.offset, curObj := s.curObj,
    curOffset := s.curOffset, best := s.best, bestWit := s.bestWit,
    chk := s.chk }

/-- The output step of the footer (CakePB `check_output`, bound side only;
testcampaign/p2b/semantics.md §2.4): `output NONE` needs nothing; `output G
FILE` needs, for `DERIVABLE`, no logged value (`best = none`); for
`EQUISATISFIABLE`, no logged and no witnessed value and checked deletion
still on; for `EQUIOPTIMAL`, an objective, checked deletion still on and the
threshold equal to the witnessed value (CakePB `bound ≤ dbound` with
`dbound ≤ bound`; the same comparison as long as the objective has not been
changed by `obju`: `best` is measured under the current objective, `bestWit`
under the original one, which agree on every solution of the core). The
comparison of
the output formula with the core (CakePB `fml_include`) is not made: the
Lean command receives no output formula, and the registered theorem is the
conclusion's, which never mentions the output claim. `IMPLICIT`,
`PERMUTATION` and `CONSTRAINTS` outputs are rejected (CakePB cannot parse
them). -/
def outputClaimOk (ctx : ConclCtx) : VeriPB.ProofStep → Bool
  | .output => true
  | .outputClaim g .file =>
    match g with
    | .derivable => ctx.best.isNone
    | .equisatisfiable => ctx.best.isNone && ctx.bestWit.isNone && ctx.chk
    | .equioptimal => !ctx.objective.isEmpty && ctx.chk && ctx.best == ctx.bestWit
  | _ => false

/-- The footer of a proof placed as VeriPB and CakePB require: the output
step and the conclusion step are the last two steps, in this order, and the
proof has no other output or conclusion step (VeriPB `conclusion.rs`
`DoubleConclusion`, `WrongFooterOrder`, `output.rs` `DoubleOutput`; CakePB
`parse_output_concl`). -/
def lastFooter (steps : Array VeriPB.ProofStep) :
    Option (VeriPB.ProofStep × VeriPB.ProofStep) :=
  match steps.toList.reverse with
  | c :: o :: rest =>
    if isConclusionStep c && isOutputStep o &&
        !rest.any (fun st => isConclusionStep st || isOutputStep st) then
      some (o, c)
    else none
  | _ => none

/-- The proof ends with a footer accepted by `outputClaimOk` and a valid
`conclusion UNSAT : id`, and logs no value (no `sol`, `soli` or `obji`):
with a logged value, a contradiction in the database only proves a lower
bound on the objective (VeriPB `ConclusionUnsatSolutionLogged`, CakePB
`HDUnsat` needs `dbound = NONE`). The same rule as the `.unsat` claim of
`conclusionClaim` (the UNSAT path `checkProofBool` and `proofClaim?` accept
the same proofs). -/
def hasUnsatConclusion (steps : Array VeriPB.ProofStep)
    (state : BoolCheckState) : Bool :=
  state.best.isNone && match lastFooter steps with
    | some (o, .conclusion id) =>
      outputClaimOk state.conclCtx o && match state.db[id]? with
        | some c => c.isContra
        | none => false
    | _ => false

/-- The claim certified by a conclusion step on a final state given by its
database lookup `getC`, formula `F` and objective context `ctx`. -/
def conclusionClaim (getC : Nat → Option Constr) (F : Array Constr)
    (ctx : ConclCtx) : VeriPB.ProofStep → Option Claim
  | .conclusion id =>
    match getC id with
    | some c =>
      if c.isContra then
        match ctx.best with
        | none => some .unsat
        -- UNSAT after a logged value: rejected (VeriPB
        -- `ConclusionUnsatSolutionLogged`; CakePB `HDUnsat` needs
        -- `dbound = NONE`)
        | some _ => none
      else none
    | none => none
  | .conclusionSat lits =>
    if satOk F ctx.objective ctx.bestWit lits then some .sat else none
  | .conclusionBounds lb hint ub lits =>
    if lowerBoundOk getC ctx.curObj ctx.curOffset ctx.best (boundOpt lb)
        hint &&
        upperBoundOk F ctx.objective ctx.offset ctx.bestWit (boundOpt ub)
          lits then
      some (.bounds (boundOpt lb) (boundOpt ub))
    else none
  | _ => none

/-! ### Orders (`def_order`, `load_order`)

Semantics: design.md §5 (testcampaign/p3), CakePB `StoreOrder`/`LoadOrder`
(npbc_checkScript.sml `check_spec`, `check_good_aord`, `check_transitivity`,
`check_reflexivity`, `guard_ord_t`). The order variables are global variable
indices; the checks run on local databases and allocate no global id. -/

/-- The `red` step of a spec block (either constructor): constraint, witness,
subproof items and closing hint. Every other statement is rejected
(CakePB `parse_spec_aux`). -/
def specRedOf : VeriPB.ProofStep →
    Option (VeriPB.OPBConstr × List (String × String) × List VeriPB.ProofStep ×
      Option Nat)
  | .red constr subst goals => some (constr, subst, goalsToItems goals, none)
  | .strengthening .red constr subst items qedHint =>
    some (constr, subst, items.toList, qedHint)
  | _ => none

/-- Well-formedness of an order encoding (CakePB `check_good_aord`):
`|left| = |right|`, the left, right and aux variables are pairwise distinct,
and every spec and def constraint ranges over them. -/
def orderWellFormed (O : Sat.PB.Dominance.OrderData) : Bool :=
  O.left.length == O.right.length &&
  decide (O.left ++ O.right ++ O.aux).Nodup &&
  (O.spec ++ O.defs).all fun c =>
    (Sat.PB.Dominance.varsOf c).all fun x => decide (x ∈ O.left ++ O.right ++ O.aux)

/-- The fresh lists of a transitivity proof (CakePB `check_ws`): `|w| = |left|`,
`|b| = |c| = |aux|`, and `left ++ right ++ aux ++ w ++ b ++ c` pairwise
distinct. -/
def transFresh (O : Sat.PB.Dominance.OrderData) (w b c : List Nat) : Bool :=
  w.length == O.left.length && b.length == O.aux.length &&
  c.length == O.aux.length &&
  decide (O.left ++ O.right ++ O.aux ++ w ++ b ++ c).Nodup

/-- Premises of the transitivity proof, ids `1..3s+2k` (CakePB `trans_subst`):
`Spec(u,v,a)`, `Spec(v,w,b)`, `Spec(u,w,c)`, `Def(u,v,a)`, `Def(v,w,b)`,
the substituted constraints normalized. -/
def transPremises (O : Sat.PB.Dominance.OrderData) (w b c : List Nat) :
    List Constr :=
  O.spec ++ O.spec.map (substGoal (Sat.PB.Dominance.sigmaVWB O w b)) ++
    O.spec.map (substGoal (Sat.PB.Dominance.sigmaUWC O w c)) ++
    O.defs ++ O.defs.map (substGoal (Sat.PB.Dominance.sigmaVWB O w b))

/-- Goals `#1..#k` of the transitivity proof: `Def(u,w,c)`. -/
def transGoals (O : Sat.PB.Dominance.OrderData) (w c : List Nat) : List Constr :=
  O.defs.map (substGoal (Sat.PB.Dominance.sigmaUWC O w c))

/-- Premises of the reflexivity proof: `Spec[v:=u]` (CakePB `refl_subst`). -/
def reflPremises (O : Sat.PB.Dominance.OrderData) : List Constr :=
  O.spec.map (substGoal (Sat.PB.Dominance.sigmaRefl O))

/-- Goals `#1..#k` of the reflexivity proof: `Def[v:=u]`. -/
def reflGoals (O : Sat.PB.Dominance.OrderData) : List Constr :=
  O.defs.map (substGoal (Sat.PB.Dominance.sigmaRefl O))

/-- Goal of a `proofgoal #j` in an order proof: the `j`-th goal (1-based);
numbered ids and `#0` are invalid (CakePB `extract_clauses` on an empty
formula). -/
def hashGoalOf (goals : List Constr) (gid : String) : Option Constr :=
  if gid.startsWith "#" then
    match (gid.drop 1).toString.toNat? with
    | some (j + 1) => goals[j]?
    | _ => none
  else none

/-- Every goal `#j, #j+1, ...` of an order proof is covered: trivial or proved
by its `proofgoal` (CakePB `check_hash_goals ([],1) [] r dsubs`, whose
implication from the trivial constraint holds only for trivial goals). -/
def hashGoalsAllCovered (proved : List (String × Constr)) :
    Nat → List Constr → Bool
  | _, [] => true
  | j, G :: gs => objuGoalCovered ("#" ++ toString j) G proved &&
      hashGoalsAllCovered proved (j + 1) gs

/-- The literals of a `load_order` (CakePB `guard_ord_t`): one per left
variable, none over an aux variable. -/
def loadOrderOk (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal) : Bool :=
  z.length == O.left.length && z.all fun l => decide (l.var ∉ O.aux)

/-- The last definition of an order name. -/
def findOrder (name : String) :
    List (String × Sat.PB.Dominance.OrderData) → Option Sat.PB.Dominance.OrderData
  | [] => none
  | (n, O) :: rest => if n == name then some O else findOrder name rest

/-- A local database for the checks of a `def_order`: the given constraints
and id counter, no core, no objective, not in a core-only subproof and not
under `strengthening_to_core` (CakePB checks spec, transitivity and
reflexivity on fresh formulas without objective). -/
def BoolCheckState.withLocalDb (state : BoolCheckState) (db : Std.HashMap Nat Constr)
    (nextId : Nat) : BoolCheckState :=
  { state with
    db := db
    nextId := nextId
    coreIds := {}
    coreOnly := false
    curObj := []
    curOffset := 0
    ord := none
    s2c := false }

/-! ### Dominance (`dom`)

The goals of `dom C : ω` with the order `(O, z)` loaded (design §5, CakePB
`dom_subgoals`), `k = |O.defs|`: `#1..#k` the order goals `Def_j[σ≤]`, `#k+1`
the strict goal (premises `Def[σ≥]`, the block derives a contradiction),
`#k+2` the objective goal `f|ω ≤ f` (only with an objective), and a goal
`Dᵢ|ω` for every CORE constraint. A goal proved inside `scope leq` (premises
`Spec[σ≤]`) or `scope geq` (premises `Spec[σ≥]`) carries that provenance:
`leq`-restricted goals count only when proved outside any scope or in
`scope leq`, the strict goal only outside any scope or in `scope geq`. -/

/-- Provenance compatible with a `leq`-restricted goal (order, objective and
core goals): proved outside any scope or in `scope leq`. -/
def provLeqOk : Option VeriPB.ScopeKind → Bool
  | none => true
  | some .leq => true
  | some .geq => false

/-- Provenance compatible with the strict goal: proved outside any scope or in
`scope geq` (CakePB `find_scope_1`). -/
def provGeqOk : Option VeriPB.ScopeKind → Bool
  | none => true
  | some .geq => true
  | some .leq => false

/-- The number of a goal id `#j`. -/
def hashNum? (gid : String) : Option Nat :=
  if gid.startsWith "#" then (gid.drop 1).toString.toNat? else none

/-- Insert constraints at consecutive ids `i, i+1, ...` (premises of a
multi-premise goal or a scope, CakePB `list_insert_fml`). -/
def insertAll : Std.HashMap Nat Constr → Nat → List Constr → Std.HashMap Nat Constr
  | db, _, [] => db
  | db, i, c :: cs => insertAll (db.insert i c) (i + 1) cs

/-- No term is over a variable of `A`. -/
def termsAuxFree (A : List Nat) (ts : List Sat.PB.Term) : Bool :=
  ts.all fun t => decide (t.2.var ∉ A)

/-- No substitution entry maps to a literal over a variable of `A`. -/
def substAuxFree (A : List Nat) (subst : List (Nat × Sat.PB.SubstVal)) : Bool :=
  subst.all fun p => (Sat.PB.Dominance.svVars p.2).all fun j => decide (j ∉ A)

/-- Freshness of the aux variables `A` of the loaded order at a `dom` step
(CakePB `check_fresh_aspo`, design T-D2): no aux variable in any database
constraint (F1), in the new constraint `nc` (normalized, F2), in the current
objective (F3), or in the image of the witness (F4). -/
def domFresh (A : List Nat) (db : Std.HashMap Nat Constr) (nc : Constr)
    (obj : Objective) (subst : List (Nat × Sat.PB.SubstVal)) : Bool :=
  db.toList.all (fun p => termsAuxFree A p.2.terms) && termsAuxFree A nc.terms &&
    termsAuxFree A obj && substAuxFree A subst

/-- Goal constraint of a `proofgoal` id in a `dom` subproof, except the strict
goal `#k+1`: `#j` (`1 ≤ j ≤ k`) the order goal `Def_j[σ≤]`, `#k+2` the
objective goal (only with an objective), a number `n` the goal `D|ω` of the
constraint `lookup n` (the database before the step, all of it). -/
def domGoalOf (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal)
    (subst : List (Nat × Sat.PB.SubstVal)) (obj : Objective)
    (lookup : Nat → Option Constr) (gid : String) : Option Constr :=
  if gid.startsWith "#" then
    match hashNum? gid with
    | some (j + 1) =>
      if j < O.defs.length then
        (O.defs[j]?).map (substGoal (Sat.PB.Dominance.sigmaLeq O z subst))
      else if j == O.defs.length + 1 && !obj.isEmpty then
        some (objGoalConstr subst obj)
      else none
    | _ => none
  else match gid.toNat? with
    | some n => (lookup n).map (substGoal subst)
    | none => none

/-- The id of the strict goal `#k+1`. -/
def domStrictId (k : Nat) (gid : String) : Bool :=
  hashNum? gid == some (k + 1)

/-- Premises of the scopes of a `dom` subproof: `Spec[σ≤]` for `scope leq`,
`Spec[σ≥]` for `scope geq` (normalized; CakePB `dom_subgoals` scopes). -/
def domScopePrem (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal)
    (subst : List (Nat × Sat.PB.SubstVal)) : VeriPB.ScopeKind → Option (List Constr)
  | .leq => some (O.spec.map (substGoal (Sat.PB.Dominance.sigmaLeq O z subst)))
  | .geq => some (O.spec.map (substGoal (Sat.PB.Dominance.sigmaGeq O z subst)))

/-- A `leq`-restricted `#` goal `G` with id `gid` is discharged: trivially
true by a complementary pair, proved with compatible provenance, or implied
by `¬C` (CakePB `check_hash_goals`). -/
def domHashCovered (nC : Constr)
    (proved : List (String × Constr × Option VeriPB.ScopeKind))
    (gid : String) (G : Constr) : Bool :=
  trivialByPair G ||
    proved.any (fun p => p.1 == gid && provLeqOk p.2.2 && constrMatchNorm G p.2.1) ||
    impliesSyntactic nC G

/-- The order goals `#j, #j+1, ...` are discharged. -/
def domOrderGoalsCovered (nC : Constr)
    (proved : List (String × Constr × Option VeriPB.ScopeKind)) :
    Nat → List Constr → Bool
  | _, [] => true
  | j, G :: gs => domHashCovered nC proved ("#" ++ toString j) G &&
      domOrderGoalsCovered nC proved (j + 1) gs

/-- The objective goal `gid` is discharged (no goal when `ω` does not touch
the objective). -/
def domObjCovered (subst : List (Nat × Sat.PB.SubstVal)) (nC : Constr)
    (obj : Objective) (proved : List (String × Constr × Option VeriPB.ScopeKind))
    (gid : String) : Bool :=
  !Sat.PB.termsAffected subst obj || domHashCovered nC proved gid (objGoalConstr subst obj)

/-- A numbered goal id that names a constraint of `goalDb`. -/
def idInDb {α : Type} (goalDb : Std.HashMap Nat α) (gid : String) : Bool :=
  !gid.startsWith "#" && match gid.toNat? with
    | some n => goalDb.contains n
    | none => false

/-- The core goal of `D` in a `dom` step needs no subproof or has one
(CakePB `subst_opt` and `split_goals`), as `dbGoalCovered` but with
provenance: equality with a proved goal counts only for goals of core ids
(`goalDb`) proved outside any scope or in `scope leq`. -/
def dbGoalCoveredDom (subst : List (Nat × Sat.PB.SubstVal)) (nC : Constr)
    (goalDb lookupDb : Std.HashMap Nat Constr)
    (proved : List (String × Constr × Option VeriPB.ScopeKind)) (D : Constr) : Bool :=
  touchedSatisfied subst D.terms ||
    (let G := substGoal subst D
     trivialByPair G ||
     impliesSyntactic (VeriPB.normalizeConstr D) G ||
     impliesSyntactic nC G ||
     proved.any (fun p => provLeqOk p.2.2 && idInDb goalDb p.1 &&
       constrMatchNorm G p.2.1) ||
     constrInDB G lookupDb)

/-! ### Redundance under a loaded order (`red`, checked `delc`)

With the order `(O, z)` loaded the goals of `red C : ω` are (design §5, CakePB
`red_subgoals`), `k = |O.defs|`: `#1` is `C|ω`, `#2..#k+1` the order goals
`Def_j[σ≤]` (skipped when `ω` maps no variable of `z`, CakePB
`skip_ord_subgoal`), `#k+2` the objective goal (only with an objective), and
the database goals as without an order. `scope leq` (premises `Spec[σ≤]`) is
allowed, `scope geq` is not (CakePB has a single scope for `red`). -/

/-- `ω` maps no variable of the loaded literals `z` (CakePB
`untouched_order_impl`; an identity entry `x -> x` counts as a touch). -/
def untouchedOrder (z : List Sat.PB.Literal) (subst : List (Nat × Sat.PB.SubstVal)) :
    Bool :=
  z.all fun l => (Sat.PB.lookupSubst subst l.var).isNone

/-- Some item of a subproof is a `scope` block (CakePB `has_scope`). -/
def hasScope (items : List VeriPB.ProofStep) : Bool :=
  items.any fun i => match i with
    | .scope _ _ => true
    | _ => false

/-- Goal constraint of a `proofgoal` id in a `red` or checked-`delc` subproof
under the loaded order `(O, z)`: `#1` is `C|ω`, `#j` (`2 ≤ j ≤ k+1`) the order
goal `Def_{j-1}[σ≤]`, `#k+2` the objective goal (only with an objective), a
number `n` the goal `D|ω` of the constraint `lookup n`. -/
def redOrdGoalOf (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr) (obj : Objective)
    (lookup : Nat → Option Constr) (gid : String) : Option Constr :=
  if gid.startsWith "#" then
    match hashNum? gid with
    | some 1 => some (substGoal subst C)
    | some (j + 2) =>
      if j < O.defs.length then
        (O.defs[j]?).map (substGoal (Sat.PB.Dominance.sigmaLeq O z subst))
      else if j == O.defs.length && !obj.isEmpty then
        some (objGoalConstr subst obj)
      else none
    | _ => none
  else match gid.toNat? with
    | some n => (lookup n).map (substGoal subst)
    | none => none

/-- Premises of the scopes of a `red` subproof under a loaded order:
`Spec[σ≤]` for `scope leq`; `scope geq` is rejected (CakePB `mk_scope`). -/
def redScopePrem (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal)
    (subst : List (Nat × Sat.PB.SubstVal)) : VeriPB.ScopeKind → Option (List Constr)
  | .leq => some (O.spec.map (substGoal (Sat.PB.Dominance.sigmaLeq O z subst)))
  | .geq => none

/-- The proved goals that count for a `leq`-restricted goal, without their
provenance (the database goals of `red` reuse `dbGoalCovered`). -/
def leqProved (proved : List (String × Constr × Option VeriPB.ScopeKind)) :
    List (String × Constr) :=
  proved.filterMap fun p => if provLeqOk p.2.2 then some (p.1, p.2.1) else none

/-- Subproof nesting depth for fuel computation: `pbc`, `red`/`dom`
(both forms), checked deletion with a subproof, `obju` and `def_order`
consume one unit; `proofgoal` and `scope` blocks run at the level of their
subproof. -/
partial def pbcDepth : List VeriPB.ProofStep → Nat
  | [] => 0
  | .pbc _ inner _ :: rest =>
    max (1 + pbcDepth inner.toList) (pbcDepth rest)
  | .red _ _ goals :: rest | .dom _ _ goals :: rest =>
    let goalDepth := goals.foldl (fun d (_, steps, _) =>
      max d (pbcDepth steps.toList)) 0
    max (1 + goalDepth) (pbcDepth rest)
  | .strengthening _ _ _ items _ :: rest =>
    max (1 + pbcDepth items.toList) (pbcDepth rest)
  | .delcChecked _ _ (some (items, _)) :: rest =>
    max (1 + pbcDepth items.toList) (pbcDepth rest)
  | .obju _ _ (some (items, _)) :: rest =>
    max (1 + pbcDepth items.toList) (pbcDepth rest)
  | .proofgoal _ steps _ :: rest =>
    max (pbcDepth steps.toList) (pbcDepth rest)
  | .scope _ items :: rest =>
    max (pbcDepth items.toList) (pbcDepth rest)
  | .defOrder od :: rest =>
    -- spec `red` steps count one more unit than they need (harmless)
    let inner := (od.spec.getD #[]).toList ++
      (match od.transitivity with
        | some t => t.proof.toList
        | none => []) ++ (od.reflexivity.getD #[]).toList
    max (1 + pbcDepth inner) (pbcDepth rest)
  | _ :: rest => pbcDepth rest

end VeriPB.Reflect
