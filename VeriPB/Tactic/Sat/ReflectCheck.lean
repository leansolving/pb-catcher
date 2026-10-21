/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import Lean
import Std
import VeriPB.Tactic.Sat.PseudoBoolean
import VeriPB.Tactic.Sat.FromVeriPB

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
it never enters `objVal` or the invariant, only the comparisons with values
written in the proof (`sol`/`soli ... : v`, `conclusion BOUNDS`).
A decision instance has the empty objective `[]`. -/
abbrev Objective := List Sat.PB.Term

/-- Objective value of a valuation. -/
def objVal (obj : Objective) (v : Valuation) : Nat := Sat.PB.evalSum v obj

/-- Check state for the Boolean checker. Uses arrays for efficiency. -/
structure BoolCheckState where
  /-- Constraint database: maps ID to constraint -/
  db : Std.HashMap Nat Constr
  /-- Original formula constraints (for solution checking); never changes
  during execution -/
  origConstrs : Array Constr
  /-- Objective function (`[]` for decision instances); never changes -/
  objective : Objective
  /-- Objective value of the best logged solution (`none` before any) -/
  best : Option Nat
  /-- Constant offset of the OPB objective: the OPB objective value of a
  valuation `v` is `objVal objective v + offset`. Never changes; used only
  to check the values written in `sol`/`soli` lines. -/
  offset : Int := 0
  /-- Next available constraint ID -/
  nextId : Nat
  /-- Number of variables -/
  numVars : Nat
  /-- Expected formula size -/
  formulaSize : Nat
  /-- Ids of the core constraints (VeriPB's core set). Bookkeeping only:
  no soundness proof uses it. It decides the `deld`/`delc` preconditions and
  which constraints a checked deletion sees (goals, hints). -/
  coreIds : Std.HashSet Nat := {}
  /-- `strengthening_to_core` mode: new `red` results go to the core. -/
  s2c : Bool := false
  deriving Inhabited

/-- Build HashMap from list with starting index (pure recursive). -/
def mkDBRec : List Constr → Nat → Std.HashMap Nat Constr
  | [], _ => {}
  | c :: rest, i => (mkDBRec rest (i + 1)).insert i c

/-- Initialize check state from an array of constraints and an objective. -/
def BoolCheckState.fromConstrs (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (offset : Int := 0) : BoolCheckState :=
  { db := mkDBRec constrs.toList 1
    origConstrs := constrs
    objective := objective
    best := none
    offset := offset
    nextId := constrs.size + 1
    numVars := numVars
    formulaSize := constrs.size
    coreIds := (List.range constrs.size).foldl (fun s i => s.insert (i + 1)) {}
    s2c := false }

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
deletion). Other ids are invalid. -/
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
or a constraint of `goalDb`. -/
def dbGoalCovered (subst : List (Nat × Sat.PB.SubstVal)) (nC : Constr)
    (goalDb : Std.HashMap Nat Constr) (proved : List (String × Constr))
    (D : Constr) : Bool :=
  touchedSatisfied subst D.terms ||
    (let G := substGoal subst D
     trivialByPair G ||
     impliesSyntactic (VeriPB.normalizeConstr D) G ||
     impliesSyntactic nC G ||
     proved.any (fun p => !p.1.startsWith "#" && constrMatchNorm G p.2) ||
     constrInDB G goalDb)

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

/-- The value written after a logged solution (`sol`/`soli lits : v`) must
equal the OPB objective value of the solution, `b' + offset` where `b'` is
its `objVal` (VeriPB `SolutionIncorrectValue`, CakePB likewise; MEM_039 §7).
No value written: nothing to check. -/
def solValueOk (offset : Int) (b' : Nat) (value : Option Int) : Bool :=
  match value with
  | none => true
  | some v => (b' : Int) + offset == v

/-- Best objective value after logging a solution of value `b'`. -/
def updBest (best : Option Nat) (b' : Nat) : Option Nat :=
  match best with
  | none => some b'
  | some b => some (min b b')

/-- Objective-improvement constraint added by `soli` for a solution of value
`b'`: the negation of `obj ≥ b'`, i.e. `Σ aᵢ¬lᵢ ≥ coeffSum − b' + 1`, which
says `obj ≤ b' − 1` (contradictory when `b' = 0`). -/
def improveConstr (obj : Objective) (b' : Nat) : Constr :=
  Constr.negate ⟨obj, b'⟩

/-- Conclusion steps (`conclusion NONE` included). -/
def isConclusionStep : VeriPB.ProofStep → Bool
  | .conclusion _ | .conclusionSat _ | .conclusionBounds _ _ _ _
  | .conclusionNone => true
  | _ => false

/-- Output steps (`output NONE` and the output claims). -/
def isOutputStep : VeriPB.ProofStep → Bool
  | .output | .outputClaim _ _ => true
  | _ => false

/-- The conclusion step of a proof whose footer is placed as VeriPB and
CakePB require (VeriPB `conclusion.rs` `DoubleConclusion` and
`WrongFooterOrder`, `output.rs` `DoubleOutput`; CakePB
`parse_output_concl`, npbc_parseProgScript.sml): the conclusion is the last
step, directly preceded by `output NONE`, and the proof has no other
conclusion or output step (the parser requires the end line after the
last step). `none` for any other placement. -/
def lastConclusion (steps : Array VeriPB.ProofStep) :
    Option VeriPB.ProofStep :=
  match steps.toList.reverse with
  | c :: .output :: rest =>
    if isConclusionStep c &&
        !rest.any (fun st => isConclusionStep st || isOutputStep st) then
      some c
    else none
  | _ => none

/-- The proof ends with a valid `conclusion UNSAT : id` (placed as
`lastConclusion` requires) and logs no solution: with a logged solution, a
contradiction in the database only proves a lower bound on the objective
(VeriPB `ConclusionUnsatSolutionLogged`, CakePB likewise). -/
def hasUnsatConclusion (steps : Array VeriPB.ProofStep)
    (state : BoolCheckState) : Bool :=
  state.best.isNone && match lastConclusion steps with
    | some (.conclusion id) => match state.db[id]? with
      | some c => c.isContra
      | none => false
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
(`none`): no logged solution and a contradictory constraint `id`. A finite
`lb`: at most the best logged value (`lb ≤ best + offset`, CakePB
`opt_le lbi dbound`), and constraint `id` syntactically implies
`objective ≥ lb − offset` (`impliesSyntactic`; a contradictory constraint
implies everything). -/
def lowerBoundOk (getC : Nat → Option Constr) (obj : Objective)
    (offset : Int) (best : Option Nat) (lb : Option Int)
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
          | some b => decide (l ≤ (b : Int) + offset)) &&
        impliesSyntactic (VeriPB.normalizeConstr D)
          (VeriPB.normalizeConstr (lowerBoundConstr obj offset l))

/-- Upper bound `ub [: lits]` of `conclusion BOUNDS` (CakePB): `INF` needs
nothing; a finite `ub` needs a solution of OPB value at most `ub`: the
solution `lits` checked against the original formula, or without `lits` the
best logged solution. -/
def upperBoundOk (F : Array Constr) (obj : Objective) (offset : Int)
    (best : Option Nat) (ub : Option Int)
    (lits : Option (List VeriPB.OPBLit)) : Bool :=
  match ub with
  | none => true
  | some u =>
    match lits with
    | none => match best with
      | none => false
      | some b => decide ((b : Int) + offset ≤ u)
    | some ls => match checkSolution F obj ls with
      | none => false
      | some val => decide ((val : Int) + offset ≤ u)

/-- `conclusion SAT [: lits]` (CakePB `HDSat`): with `lits`, a solution of
the original formula; without, some logged solution. -/
def satOk (F : Array Constr) (obj : Objective) (best : Option Nat)
    (lits : Option (List VeriPB.OPBLit)) : Bool :=
  match lits with
  | none => best.isSome
  | some ls => (checkSolution F obj ls).isSome

/-- The claim certified by a conclusion step on a final state given by its
database lookup `getC`, formula `F`, objective, offset and best value. -/
def conclusionClaim (getC : Nat → Option Constr) (F : Array Constr)
    (obj : Objective) (offset : Int) (best : Option Nat) :
    VeriPB.ProofStep → Option Claim
  | .conclusion id =>
    match getC id with
    | some c =>
      if c.isContra then
        match best with
        | none => some .unsat
        -- UNSAT after a logged solution: rejected (VeriPB
        -- `ConclusionUnsatSolutionLogged`; CakePB `HDUnsat` needs
        -- `dbound = NONE`)
        | some _ => none
      else none
    | none => none
  | .conclusionSat lits => if satOk F obj best lits then some .sat else none
  | .conclusionBounds lb hint ub lits =>
    if lowerBoundOk getC obj offset best (boundOpt lb) hint &&
        upperBoundOk F obj offset best (boundOpt ub) lits then
      some (.bounds (boundOpt lb) (boundOpt ub))
    else none
  | _ => none

/-- Subproof nesting depth for fuel computation: `pbc`, `red`/`dom`
(both forms) and checked deletion with a subproof consume one unit; a
`proofgoal` block runs at the level of its subproof. -/
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
  | .proofgoal _ steps _ :: rest =>
    max (pbcDepth steps.toList) (pbcDepth rest)
  | _ :: rest => pbcDepth rest

end VeriPB.Reflect
