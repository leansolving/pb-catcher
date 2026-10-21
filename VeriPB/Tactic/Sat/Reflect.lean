/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import Lean
import Std
import VeriPB.Tactic.Sat.PseudoBoolean
import VeriPB.Tactic.Sat.FromVeriPB
import VeriPB.Tactic.Sat.ReflectCheck
import VeriPB.Tactic.Sat.ReflectFast

/-!
# Reflection-based VeriPB Proof Checking

This module provides a reflection-based approach to VeriPB proof verification.
Instead of building kernel proof terms for each step, we:

1. Define a checker function `checkProof : ... → Bool`
2. Prove soundness: `checkProof = true → formula is UNSAT`
3. Use `native_decide` to evaluate `checkProof` efficiently

This approach scales much better than explicit Expr construction because:
- The kernel proof term is tiny (just the soundness theorem + native_decide)
- The heavy computation runs as compiled Lean code, not kernel reduction
- Memory usage is bounded by the checker state, not accumulated Expr nodes

The checker components it builds on live in two companion modules:
`VeriPB.Tactic.Sat.ReflectCheck` (list-based, the definitions the proofs
reason about) and `VeriPB.Tactic.Sat.ReflectFast` (array-based runtime
replacement).  The step loop itself stays here, next to its soundness
proofs.  This module ties the two checkers together with
`@[implemented_by]`, proves soundness, and provides the `veripb_reflect`
command.

## Trust assumptions

Using `native_decide` adds the Lean compiler to the trusted code base.
This is the same trust model as Lean's built-in `bv_decide` tactic.

## Main definitions

* `VeriPB.Reflect.checkProofBool` — Boolean checker for VeriPB proofs
* `VeriPB.Reflect.StateInv` — optimization-preserving invariant (every
  solution of the formula that beats the best logged objective value has a
  database counterpart that is at least as good), preserved by every step
  (`execStepsFuel_inv_preserve`); redundance steps are checked by
  `checkRedundance` (subproof items by `processRedItems`), and subproofs use
  the implication lemma `execStepsFuel_implied` (their `lstep`s keep every
  valuation of the database)
* `VeriPB.Reflect.checkProof_sound` — Soundness theorem (UNSAT)
* `VeriPB.Reflect.execStepsFuel_bounds` — optimality of the best logged
  solution after a contradiction (for later bounds theorems)
* `VeriPB.Reflect.Fast.checkProofBoolFast` — Array-based runtime replacement
  via `@[implemented_by]`
* `VeriPB.Reflect.mkFormulaUnsatProof` — Reflection bridge term for
  external `formulaUnsat` proofs (downstream entry point)
* `veripb_reflect` — Command using reflection
-/

namespace VeriPB.Reflect

open Sat.PB

/-! ### Step execution (total, fuel-bounded) -/

/-- Process the items of a redundance subproof (`red`, checked `delc`),
CakePB `check_scopes`/`check_subproofs`: a top-level step (an `lstep`) runs
on the current subproof database and its result stays visible to later
items; a `proofgoal gid ... qed : h` block runs on the current database plus
the negated goal constraint `goalOf gid` and must derive the contradictory
constraint `h`, after which its constraints are dropped (only the id counter
advances). A `proofgoal` without a closing id and `scope` blocks are
rejected. Returns the final subproof state and the proved goals with their
constraints. `execFn` is the step executor (`execStepsFuel` at the next
fuel level). -/
def processRedItems
    (execFn : BoolCheckState → List VeriPB.ProofStep → Option BoolCheckState)
    (goalOf : String → Option Constr) :
    BoolCheckState → List VeriPB.ProofStep → List (String × Constr) →
      Option (BoolCheckState × List (String × Constr))
  | st, [], proved => some (st, proved)
  | st, item :: rest, proved =>
    match item with
    | .proofgoal gid steps (some h) =>
      if steps.any innerStepForbidden then none else
      match goalOf gid with
      | none => none
      | some G =>
        let sub := { st with
          db := st.db.insert st.nextId (negTriv G)
          nextId := st.nextId + 1 }
        match execFn sub steps.toList with
        | none => none
        | some fin =>
          match fin.db[h]? with
          | some c =>
            if c.isContra then
              processRedItems execFn goalOf { st with nextId := fin.nextId } rest
                ((gid, G) :: proved)
            else none
          | none => none
    | _ =>
      if isLStep item then
        match execFn st [item] with
        | some st' => processRedItems execFn goalOf st' rest proved
        | none => none
      else none

/-- Redundance check of `C` with witness `subst` (CakePB `check_red`):
`¬C` (normalized, `rupNegate`) is added at `st0.nextId`, the subproof items
run, and then either the closing hint `qed : cid` names a contradictory
constraint (every goal is discharged), or the `#` goals and every database
goal over `goalDb` are covered. Returns the next free id after the
subproof. -/
def checkRedundance
    (execFn : BoolCheckState → List VeriPB.ProofStep → Option BoolCheckState)
    (st0 : BoolCheckState) (goalDb : Std.HashMap Nat Constr)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List VeriPB.ProofStep) (qedHint : Option Nat) : Option Nat :=
  let nC := rupNegate C
  let st1 := { st0 with
    db := st0.db.insert st0.nextId nC
    nextId := st0.nextId + 1 }
  match processRedItems execFn (redGoalOf subst C st0.objective goalDb) st1
      items [] with
  | none => none
  | some (fin, proved) =>
    let ok := match qedHint with
      | some cid => match fin.db[cid]? with
        | some c => c.isContra
        | none => false
      | none =>
        hashGoalsCovered subst C nC st0.objective proved &&
        goalDb.toList.all fun (_, D) => dbGoalCovered subst nC goalDb proved D
    if ok then some fin.nextId else none

/-- Redundance-based strengthening `red C : ω` with subproof `items`: the
redundance check against the whole database (core and derived), then `C`
(normalized) is added after the subproof's ids, to the core iff
`strengthening_to_core` is on. -/
def redStep
    (execFn : BoolCheckState → List VeriPB.ProofStep → Option BoolCheckState)
    (state : BoolCheckState) (constr : VeriPB.OPBConstr)
    (substPairs : List (String × String)) (items : List VeriPB.ProofStep)
    (qedHint : Option Nat) : Option BoolCheckState :=
  match VeriPB.opbConstrToPB constr with
  | .error _ => none
  | .ok C =>
    match VeriPB.parseSubstPairs substPairs state.numVars with
    | .error _ => none
    | .ok subst =>
      match checkRedundance execFn state state.db subst C items qedHint with
      | none => none
      | some fid =>
        some { state with
          db := state.db.insert fid (VeriPB.normalizeConstr C)
          nextId := fid + 1
          coreIds := if state.s2c then state.coreIds.insert fid else state.coreIds }

/-- Checked deletion `delc id : ω : subproof ... qed [: cid]` (CakePB
`CheckedDelete`): exactly one id, which must be core, and a subproof
(VeriPB's autoproved form is not accepted); under
`strengthening_to_core` the subproof must end with `qed : cid` (CakePB
`check_tcb_idopt`; VeriPB's extra empty-witness requirement is not
imposed). The constraint is erased, then the redundance check runs
with `C := D` against the remaining core constraints only (the subproof sees
only them). The check is for parity with VeriPB/CakePB: erasing a constraint
preserves the invariant on its own, so the soundness proofs only use that
the step erases one id. -/
def delcCheckedStep
    (execFn : BoolCheckState → List VeriPB.ProofStep → Option BoolCheckState)
    (state : BoolCheckState) (ids : List Nat)
    (substPairs : List (String × String))
    (sub : Option (Array VeriPB.ProofStep × Option Nat)) :
    Option BoolCheckState :=
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
          match checkRedundance execFn
              { state with db := coreDb, coreIds := core' } coreDb subst D
              items.toList qedHint with
          | none => none
          | some fid =>
            some { state with db := rest, coreIds := core', nextId := fid }
  | _, _ => none

/-- Execute proof steps with fuel for subproof nesting depth.
    Returns the final state if all steps succeed.
    Fuel is consumed only by subproofs (`pbc`, `red`, checked `delc`). -/
def execStepsFuel (fuel : Nat) (state : BoolCheckState)
    (steps : List VeriPB.ProofStep) : Option BoolCheckState :=
  match steps with
  | [] => some state
  | step :: rest =>
    let stepResult : Option BoolCheckState := match step with
      | .formulaSize n =>
        if state.formulaSize != n then none else some state
      | .pol ops =>
        match execPolRPNBool ops state.db with
        | some result =>
          let newDb := state.db.insert state.nextId
            (VeriPB.normalizeConstr result)
          some { state with db := newDb, nextId := state.nextId + 1 }
        | none => none
      | .rup constr hints =>
        match VeriPB.opbConstrToPB constr with
        | .ok pbConstr =>
          if !verifyRupBool (rupNegate pbConstr) hints state.db
              state.numVars then none
          else
            let newDb := state.db.insert state.nextId
              (VeriPB.normalizeConstr pbConstr)
            some { state with db := newDb, nextId := state.nextId + 1 }
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
              if impliesSyntactic (VeriPB.normalizeConstr S)
                  (VeriPB.normalizeConstr T0) then
                some { state with
                  db := state.db.insert state.nextId (VeriPB.normalizeConstr T0)
                  nextId := state.nextId + 1 }
              else none
      | .pbc constr innerSteps resultId =>
        if innerSteps.any innerStepForbidden then none
        else match fuel with
        | 0 => none
        | n + 1 =>
          match VeriPB.opbConstrToPB constr with
          | .ok pbConstr =>
            if pbConstr.degree > pbConstr.coeffSum then none
            else
              let savedDb := state.db
              let negId := state.nextId
              let dbWithNeg := state.db.insert negId pbConstr.negate
              let subState : BoolCheckState :=
                { state with db := dbWithNeg, nextId := negId + 1 }
              match execStepsFuel n subState innerSteps.toList with
              | some finalSub =>
                match finalSub.db[resultId]? with
                | some c =>
                  if !c.isContra then none
                  else
                    let restoredDb := savedDb.insert finalSub.nextId
                      (VeriPB.normalizeConstr pbConstr)
                    some { state with
                      db := restoredDb
                      nextId := finalSub.nextId + 1 }
                | none => none
              | none => none
          | .error _ => none
      | .red constr substPairs goals =>
        match fuel with
        | 0 => none
        | n + 1 =>
          redStep (execStepsFuel n) state constr substPairs (goalsToItems goals) none
      | .strengthening rule constr substPairs items qedHint =>
        match rule with
        | .dom => none  -- dominance needs an order (P3)
        | .red =>
          match fuel with
          | 0 => none
          | n + 1 =>
            redStep (execStepsFuel n) state constr substPairs items.toList qedHint
      | .delcChecked ids substPairs sub =>
        match fuel with
        | 0 => none
        | n + 1 => delcCheckedStep (execStepsFuel n) state ids substPairs sub
      | .deld ids =>
        -- `deld` deletes derived constraints only (VeriPB, CakePB)
        if ids.any state.coreIds.contains then none
        else some { state with
          db := ids.foldl (fun db id => db.erase id) state.db
          coreIds := ids.foldl (fun s id => s.erase id) state.coreIds }
      | .delc ids =>
        -- unchecked deletion; under `strengthening_to_core` CakePB requires
        -- every constraint to be core
        if state.s2c && !allCore state then none
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
        if on then some { state with coreIds := allIds state.db, s2c := true }
        else some { state with s2c := false }
      | .loadOrder (some _) _ => none  -- orders are not supported (P3)
      | .loadOrder none _ => some state  -- unloading: no order is ever loaded
      | .defOrder _ => some state  -- allocates no ids; orders are not used
      | .output => some state
      | .conclusionNone => some state
      | .conclusion id =>
        match state.db[id]? with
        | some c => if c.isContra then some state else none
        | none => none
      | .sol lits value =>
        match checkSolution state.origConstrs state.objective lits with
        | none => none
        | some b' =>
          if !solValueOk state.offset b' value then none
          else some { state with best := updBest state.best b' }
      | .soli lits value =>
        match checkSolution state.origConstrs state.objective lits with
        | none => none
        | some b' =>
          if !solValueOk state.offset b' value then none
          else some { state with
            db := state.db.insert state.nextId
              (improveConstr state.objective b')
            nextId := state.nextId + 1
            best := updBest state.best b'
            coreIds := state.coreIds.insert state.nextId }
      | .conclusionSat _ => some state
      | .conclusionBounds _ _ _ _ => some state
      | _ => none  -- statements the checker does not support yet
    match stepResult with
    | some s => execStepsFuel fuel s rest
    | none => none
termination_by (fuel, steps.length)

/-- Main Boolean checker: returns true iff the proof is a valid UNSAT proof
of `constrs` (logging no solution) with respect to `objective` (`[]` for
decision instances; the objective only matters for `sol`/`soli` and for
the red witness check). `names` lists the formula's variables that are not
written `x<N>`, with their indices (`VeriPB.OPBInstance.names`, `[]` when
all are `x<N>`); the proof parser needs them to resolve such names. The
checker's variable count is `numVars` raised to the parser's count, which
includes the fresh (extension) variables the proof introduces. -/
@[implemented_by Fast.checkProofBoolFast]
def checkProofBool (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (names : List (String × Nat))
    (proofStr : String) : Bool :=
  match VeriPB.parseVeriPBProofWith (VeriPB.VarTable.ofList names numVars)
      proofStr with
  | .error _ => false
  | .ok proofData =>
    let initState := BoolCheckState.fromConstrs constrs
      (max numVars proofData.numVars) objective
    let fuel := pbcDepth proofData.steps.toList + 1
    match execStepsFuel fuel initState proofData.steps.toList with
    | some finalState =>
      hasUnsatConclusion proofData.steps finalState
    | none => false

/-- Checker for every conclusion kind: runs the proof like `checkProofBool`
(with the objective's constant `offset`, which the `sol`/`soli` values are
checked against) and returns the claim its last conclusion step certifies
on the final state (`conclusionClaim`), or `none` if a step or the
conclusion is rejected. `checkProofClaim_sound` gives the meaning
(`Claim.holds`). -/
@[implemented_by Fast.proofClaimFast?]
def proofClaim? (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (offset : Int) (names : List (String × Nat))
    (proofStr : String) : Option Claim :=
  match VeriPB.parseVeriPBProofWith (VeriPB.VarTable.ofList names numVars)
      proofStr with
  | .error _ => none
  | .ok proofData =>
    let initState := BoolCheckState.fromConstrs constrs
      (max numVars proofData.numVars) objective offset
    let fuel := pbcDepth proofData.steps.toList + 1
    match execStepsFuel fuel initState proofData.steps.toList with
    | some s =>
      match lastConclusion proofData.steps with
      | some step =>
        conclusionClaim (fun id => s.db[id]?) constrs objective offset s.best
          step
      | none => none
    | none => none

/-- Boolean entry point for native evaluation: the proof certifies `claim`. -/
def checkProofClaimBool (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (offset : Int) (names : List (String × Nat))
    (proofStr : String) (claim : Claim) : Bool :=
  decide (proofClaim? constrs numVars objective offset names proofStr =
    some claim)

/-! ## Soundness theorem infrastructure -/

/-- A formula is unsatisfiable if no valuation satisfies all constraints. -/
def formulaUnsat (constrs : Array Constr) : Prop :=
  ∀ v : Valuation, ∃ c ∈ constrs.toList, ¬c.sat v

/-- Legacy alias: implication-based soundness (stronger than DBPreserve).
    Every constraint in db is a consequence of the original formula.
    Used for pol/rup/pbc steps where the added constraint is implied. -/
def DBSound (original : Array Constr) (db : Std.HashMap Nat Constr) : Prop :=
  ∀ (id : Nat) (c : Constr), db.get? id = some c →
    ∀ v : Valuation, (∀ c' ∈ original.toList, Constr.sat c' v) →
      Constr.sat c v

/-- DB satisfiability: there exists a valuation satisfying all DB entries.
    Weaker than DBSound (no formula reference). Preserved by all proof steps
    except solution logging, which is rejected inside subproofs; this is the
    invariant for `pbc` and `red` subproofs. The top-level invariant is
    `StateInv`. -/
def DBSat (db : Std.HashMap Nat Constr) : Prop :=
  ∃ v : Valuation, ∀ (id : Nat) (c : Constr), db.get? id = some c →
    Constr.sat c v

/-- `w` satisfies every database entry. -/
def DBSatBy (db : Std.HashMap Nat Constr) (w : Valuation) : Prop :=
  ∀ (id : Nat) (c : Constr), db.get? id = some c → Constr.sat c w

/-- Bridge: construct a synthetic DBSound from a HashMap by using its
    toList values as the "formula". This lets us reuse existing pol/rup
    soundness lemmas in the DBSat-based proof. -/
theorem DBSound_of_toList (db : Std.HashMap Nat Constr) :
    DBSound ⟨db.toList.map Prod.snd⟩ db := by
  intro id c hget v hsat
  have hmem : (id, c) ∈ db.toList := by
    rw [Std.HashMap.get?_eq_getElem?] at hget
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget
  have : c ∈ db.toList.map Prod.snd :=
    List.mem_map.mpr ⟨(id, c), hmem, rfl⟩
  exact hsat c (by simpa using this)

/-- The toList-based formula is satisfied by any valuation satisfying the DB. -/
theorem toList_sat_of_DBSat (db : Std.HashMap Nat Constr) (v : Valuation)
    (hdb : ∀ id c, db.get? id = some c → Constr.sat c v) :
    ∀ c ∈ (⟨db.toList.map Prod.snd⟩ : Array Constr).toList, Constr.sat c v := by
  intro c hmem
  have hmem' : c ∈ db.toList.map Prod.snd := by simpa using hmem
  obtain ⟨⟨id, _⟩, hmem'', rfl⟩ := List.mem_map.mp hmem'
  exact hdb id _ (by
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem'')

theorem DBSat_erase (db : Std.HashMap Nat Constr) (id : Nat)
    (hsat : DBSat db) : DBSat (db.erase id) := by
  obtain ⟨v, hv⟩ := hsat
  exact ⟨v, fun id' c hget => hv id' c (by
    simp only [Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_erase] at hget ⊢
    by_cases heq : id == id'
    · simp [heq] at hget
    · simp [heq] at hget; exact hget)⟩

theorem DBSat_erase_fold (db : Std.HashMap Nat Constr) (ids : List Nat)
    (hsat : DBSat db) :
    DBSat (ids.foldl (fun db id => db.erase id) db) := by
  induction ids generalizing db with
  | nil => exact hsat
  | cons id rest ih => exact ih (db.erase id) (DBSat_erase db id hsat)

-- HashMap helper lemmas

theorem HashMap_get?_empty (k : Nat) :
    (∅ : Std.HashMap Nat Constr).get? k = none := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]

theorem HashMap_get?_insert (m : Std.HashMap Nat Constr) (k k' : Nat)
    (c : Constr) :
    (m.insert k c).get? k' = if k == k' then some c else m.get? k' := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem DBSat_insert_dbImplied (db : Std.HashMap Nat Constr)
    (id : Nat) (c : Constr) (hsat : DBSat db)
    (himpl : ∀ v, (∀ id' c', db.get? id' = some c' → Constr.sat c' v) →
      Constr.sat c v) :
    DBSat (db.insert id c) := by
  obtain ⟨v, hv⟩ := hsat
  exact ⟨v, fun id' c' hget => by
    rw [HashMap_get?_insert] at hget
    by_cases heq : id == id'
    · simp [heq] at hget; subst hget; exact himpl v hv
    · simp [heq] at hget; exact hv id' c' hget⟩

-- mkDBRec properties

theorem mkDBRec_mem (cs : List Constr) (startIdx : Nat) (id : Nat)
    (c : Constr) :
    (mkDBRec cs startIdx).get? id = some c → c ∈ cs := by
  induction cs generalizing startIdx with
  | nil =>
    simp only [mkDBRec]
    intro h; rw [HashMap_get?_empty] at h; cases h
  | cons hd tl ih =>
    simp only [mkDBRec]
    intro hget; rw [HashMap_get?_insert] at hget
    by_cases heq : startIdx == id
    · simp only [heq, ↓reduceIte] at hget
      injection hget with hc; subst hc
      exact List.Mem.head _
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hget
      exact List.Mem.tail _ (ih (startIdx + 1) hget)

theorem init_sound (constrs : Array Constr) (numVars : Nat) (obj : Objective) :
    DBSound constrs (BoolCheckState.fromConstrs constrs numVars obj).db :=
  fun id c hc v hsat => by
    simp only [BoolCheckState.fromConstrs] at hc
    exact hsat c (mkDBRec_mem constrs.toList 1 id c hc)

/-! ## Soundness proofs -/

-- normalize_sat: normalization preserves satisfaction

theorem evalSum_singleton (v : Valuation) (t : Nat × Sat.PB.Literal) :
    Sat.PB.evalSum v [t] = t.1 * Sat.PB.evalLit v t.2 := by
  simp [Sat.PB.evalSum]

theorem list_take_drop_get (l : List α) (i : Nat) (hi : i < l.length) :
    l = l.take i ++ [l[i]] ++ l.drop (i + 1) := by
  induction l generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
    cases i with
    | zero => simp [List.take, List.drop]
    | succ j =>
      simp only [List.take_succ_cons, List.drop_succ_cons,
                 List.getElem_cons_succ, List.cons_append]
      congr 1
      have hj : j < xs.length := by
        simp only [List.length_cons] at hi; omega
      exact ih j hj

theorem evalSum_remove_zero (v : Valuation) (l : List (Nat × Sat.PB.Literal))
    (i : Nat) (hi : i < l.length) (hzero : l[i].1 = 0) :
    Sat.PB.evalSum v (l.take i ++ l.drop (i + 1)) =
      Sat.PB.evalSum v l := by
  have hdecomp := list_take_drop_get l i hi
  have hlhs : Sat.PB.evalSum v (l.take i ++ l.drop (i + 1)) =
    Sat.PB.evalSum v (l.take i) + Sat.PB.evalSum v (l.drop (i + 1)) :=
    Sat.PB.evalSum_append v _ _
  have hrhs1 : Sat.PB.evalSum v l =
    Sat.PB.evalSum v (l.take i ++ [l[i]] ++ l.drop (i + 1)) :=
    congrArg (Sat.PB.evalSum v) hdecomp
  have hrhs2 :
    Sat.PB.evalSum v (l.take i ++ [l[i]] ++ l.drop (i + 1)) =
    Sat.PB.evalSum v (l.take i ++ [l[i]]) +
      Sat.PB.evalSum v (l.drop (i + 1)) :=
    Sat.PB.evalSum_append v _ _
  have hrhs3 : Sat.PB.evalSum v (l.take i ++ [l[i]]) =
    Sat.PB.evalSum v (l.take i) + Sat.PB.evalSum v [l[i]] :=
    Sat.PB.evalSum_append v _ _
  have hmid : Sat.PB.evalSum v [l[i]] = 0 := by
    rw [evalSum_singleton, hzero]; simp
  calc Sat.PB.evalSum v (l.take i ++ l.drop (i + 1))
      = Sat.PB.evalSum v (l.take i) +
        Sat.PB.evalSum v (l.drop (i + 1)) := hlhs
    _ = Sat.PB.evalSum v (l.take i) + 0 +
        Sat.PB.evalSum v (l.drop (i + 1)) := by omega
    _ = Sat.PB.evalSum v (l.take i) + Sat.PB.evalSum v [l[i]] +
        Sat.PB.evalSum v (l.drop (i + 1)) := by rw [hmid]
    _ = Sat.PB.evalSum v (l.take i ++ [l[i]]) +
        Sat.PB.evalSum v (l.drop (i + 1)) := by rw [← hrhs3]
    _ = Sat.PB.evalSum v (l.take i ++ [l[i]] ++ l.drop (i + 1)) := by
        rw [← hrhs2]
    _ = Sat.PB.evalSum v l := by rw [← hrhs1]

-- findIdx helper lemmas

theorem findIdx_go_lt (l : List α) (p : α → Bool) (n i : Nat) :
    List.findIdx?.go p l n = some i → i < n + l.length := by
  induction l generalizing n i with
  | nil => intro h; simp only [List.findIdx?.go] at h; cases h
  | cons x xs ih =>
    intro h; simp only [List.findIdx?.go] at h
    by_cases hp : p x
    · simp [hp] at h; simp only [← h, List.length_cons]; omega
    · simp [hp] at h
      have := ih (n + 1) i h; simp only [List.length_cons]; omega

theorem findZeroIdx_lt (terms : List Sat.PB.Term) (idx : Nat)
    (h : VeriPB.findZeroIdx terms = some idx) : idx < terms.length := by
  simp only [VeriPB.findZeroIdx] at h
  have := findIdx_go_lt terms _ 0 idx h; omega

theorem findIdx_go_ge (l : List α) (p : α → Bool) (n i : Nat) :
    List.findIdx?.go p l n = some i → n ≤ i := by
  induction l generalizing n i with
  | nil => intro h; simp only [List.findIdx?.go] at h; cases h
  | cons x xs ih =>
    intro h; simp only [List.findIdx?.go] at h
    by_cases hp : p x
    · simp [hp] at h; omega
    · simp [hp] at h; have := ih (n + 1) i h; omega

theorem findIdx_go_getElem? (l : List α) (p : α → Bool) (n i : Nat)
    (h : List.findIdx?.go p l n = some i) :
    ∃ x, l[i - n]? = some x ∧ p x = true := by
  induction l generalizing n with
  | nil => simp [List.findIdx?.go] at h
  | cons x xs ih =>
    simp only [List.findIdx?.go] at h
    by_cases hp : p x
    · simp [hp] at h; subst h
      refine ⟨x, ?_, hp⟩; simp [Nat.sub_self]
    · simp [hp] at h
      have hge : n + 1 ≤ i := findIdx_go_ge xs p (n + 1) i h
      obtain ⟨y, hget, hpy⟩ := ih (n + 1) h
      refine ⟨y, ?_, hpy⟩
      have heq : i - n = (i - (n + 1)) + 1 := by omega
      simp only [heq, List.getElem?_cons_succ]; exact hget

theorem findZeroIdx_zero (terms : List Sat.PB.Term) (idx : Nat)
    (hlt : idx < terms.length)
    (h : VeriPB.findZeroIdx terms = some idx) : terms[idx].1 = 0 := by
  simp only [VeriPB.findZeroIdx] at h
  obtain ⟨x, hget, hpred⟩ :=
    findIdx_go_getElem? terms (fun (c, _) => c == 0) 0 idx h
  simp at hget
  have heq : terms[idx] = x := by
    rw [List.getElem?_eq_some_iff] at hget; exact hget.2
  rw [heq]; simp at hpred; exact hpred

-- Literal BEq-to-Eq bridge

private theorem Literal_beq_eq (l1 l2 : Sat.PB.Literal) :
    (l1 == l2) = true → l1 = l2 := by
  intro h; cases l1 <;> cases l2 <;>
    simp [BEq.beq, Sat.PB.instBEqLiteral.beq] at h <;> simp [h]

-- Two-point list decomposition

private theorem list_two_point_decomp {α : Type} (l : List α)
    (i j : Nat) (hi : i < l.length) (hj : j < l.length)
    (hij : i < j) :
    l = l.take i ++ l[i] ::
      (l.drop (i + 1)).take (j - i - 1) ++
        l[j] :: l.drop (j + 1) := by
  have hlen : j - i - 1 < (l.drop (i + 1)).length := by
    simp [List.length_drop]; omega
  have eq_inner_drop : (l.drop (i + 1)).drop (j - i - 1) =
      l[j] :: l.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hlen]
    congr 1
    · simp [List.getElem_drop]; congr 1; omega
    · rw [List.drop_drop]; congr 1; omega
  have eq_inner : l.drop (i + 1) =
      (l.drop (i + 1)).take (j - i - 1) ++
        l[j] :: l.drop (j + 1) := by
    have h := (List.take_append_drop (j - i - 1)
      (l.drop (i + 1))).symm
    rw [eq_inner_drop] at h; exact h
  have eq_outer := (List.take_append_drop i l).symm
  rw [List.drop_eq_getElem_cons hi] at eq_outer
  rw [eq_inner] at eq_outer
  have reassoc : ∀ (a : α) (xs ys zs : List α),
      xs ++ a :: (ys ++ zs) = (xs ++ a :: ys) ++ zs := by
    intros; simp [List.append_assoc, List.cons_append]
  rw [reassoc] at eq_outer
  exact eq_outer

-- normalize_sat proof via go_sat

theorem go_sat (fuel : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (v : Valuation) (h : Sat.PB.evalSum v terms ≥ degree) :
    (VeriPB.normalizeConstr.go fuel terms degree).sat v := by
  induction fuel generalizing terms degree with
  | zero => simp only [VeriPB.normalizeConstr.go]; exact h
  | succ n ih =>
    simp only [VeriPB.normalizeConstr.go]
    cases hzero : VeriPB.findZeroIdx terms with
    | some idx =>
      apply ih; have hidx := findZeroIdx_lt terms idx hzero
      have hcoeff := findZeroIdx_zero terms idx hidx hzero
      rw [evalSum_remove_zero v terms idx hidx hcoeff]; exact h
    | none =>
      cases hpair : VeriPB.findValidCompPairIdx terms degree with
      | some pair =>
        obtain ⟨i, j⟩ := pair
        simp only []
        -- Split through guards: hi, hj, hij, hlit, hle
        split
        · split
          · split
            · split
              · split
                · next hi hj hij hlit hle =>
                  apply ih
                  have hlit_eq := Literal_beq_eq _ _ hlit
                  have hj_eq : terms[j] =
                      (terms[j].1, terms[i].2.negate) :=
                    Prod.ext rfl hlit_eq
                  have hdecomp := list_two_point_decomp
                    terms i j hi hj hij
                  have hform : (Constr.mk terms degree).sat v :=
                    h
                  rw [hdecomp, hj_eq] at hform
                  exact cancel_pair_sat v (terms.take i)
                    ((terms.drop (i + 1)).take (j - i - 1))
                    (terms.drop (j + 1)) terms[i].2
                    terms[i].1 terms[j].1 degree hle hform
                · exact h
              · exact h
            · exact h
          · exact h
        · exact h
      | none =>
        cases hlike : VeriPB.findLikeTermIdx terms with
        | some pair =>
          obtain ⟨i, j⟩ := pair
          simp only []
          -- Split through guards: hi, hj, hij, hlit
          split
          · split
            · split
              · split
                · next hi hj hij hlit =>
                  apply ih
                  have hlit_eq := Literal_beq_eq _ _ hlit
                  have hj_eq : terms[j] =
                      (terms[j].1, terms[i].2) :=
                    Prod.ext rfl hlit_eq
                  have hdecomp := list_two_point_decomp
                    terms i j hi hj hij
                  have hform :
                      (Constr.mk terms degree).sat v := h
                  rw [hdecomp, hj_eq] at hform
                  exact merge_terms_sat v (terms.take i)
                    ((terms.drop (i + 1)).take (j - i - 1))
                    (terms.drop (j + 1)) terms[i].2
                    terms[i].1 terms[j].1 degree hform
                · exact h
              · exact h
            · exact h
          · exact h
        | none => exact h

theorem normalize_sat (c : Constr) (v : Valuation) (h : c.sat v) :
    (VeriPB.normalizeConstr c).sat v := by
  simp only [VeriPB.normalizeConstr, Constr.sat] at *
  exact go_sat _ _ _ v h

instance : LawfulBEq Sat.PB.Literal where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;>
      simp only [BEq.beq, Sat.PB.instBEqLiteral.beq] at h <;>
      (try exact absurd h Bool.false_ne_true)
    all_goals exact congrArg _ (of_decide_eq_true h)
  rfl {a} := by
    cases a <;> simp only [BEq.beq, Sat.PB.instBEqLiteral.beq] <;>
      exact decide_eq_true trivial

/-! ### Reverse normalization (for constrInDB soundness) -/

private theorem cancel_pair_sat_rev (v : Valuation) (pre mid post : List Sat.PB.Term)
    (l : Sat.PB.Literal) (a b d : Nat) (hle : min a b ≤ d)
    (h : (Constr.mk (pre ++ (a - min a b, l) :: mid ++
      (b - min a b, l.negate) :: post) (d - min a b)).sat v) :
    (Constr.mk (pre ++ (a, l) :: mid ++ (b, l.negate) :: post) d).sat v := by
  simp only [Constr.sat] at *
  have hkey := Sat.PB.complementary_sum v l a b
  rw [Sat.PB.evalSum_append] at h ⊢
  simp only [Sat.PB.evalSum] at h ⊢
  rw [Sat.PB.evalSum_append] at h ⊢
  simp only [Sat.PB.evalSum] at h ⊢
  omega

private theorem remove_zero_sat_rev (v : Valuation) (pre post : List Sat.PB.Term)
    (l : Sat.PB.Literal) (d : Nat)
    (h : (Constr.mk (pre ++ post) d).sat v) :
    (Constr.mk (pre ++ (0, l) :: post) d).sat v := by
  simp only [Constr.sat] at *
  rw [Sat.PB.evalSum_append] at h ⊢
  simp only [Sat.PB.evalSum] at h ⊢
  omega

private theorem merge_terms_sat_rev (v : Valuation) (pre mid post : List Sat.PB.Term)
    (l : Sat.PB.Literal) (a b d : Nat)
    (h : (Constr.mk (pre ++ (a + b, l) :: mid ++ post) d).sat v) :
    (Constr.mk (pre ++ (a, l) :: mid ++ (b, l) :: post) d).sat v := by
  simp only [Constr.sat] at *
  rw [Sat.PB.evalSum_append] at h ⊢
  simp only [Sat.PB.evalSum] at h ⊢
  rw [Sat.PB.evalSum_append] at h ⊢
  simp only [Sat.PB.evalSum] at h ⊢
  have hm : (a + b) * Sat.PB.evalLit v l = a * Sat.PB.evalLit v l + b * Sat.PB.evalLit v l :=
    Nat.add_mul a b _
  omega

theorem go_sat_rev (fuel : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (v : Valuation) (h : (VeriPB.normalizeConstr.go fuel terms degree).sat v) :
    Sat.PB.evalSum v terms ≥ degree := by
  induction fuel generalizing terms degree with
  | zero => simp only [VeriPB.normalizeConstr.go] at h; exact h
  | succ n ih =>
    simp only [VeriPB.normalizeConstr.go] at h
    cases hzero : VeriPB.findZeroIdx terms with
    | some idx =>
      rw [hzero] at h
      have hidx := findZeroIdx_lt terms idx hzero
      have hcoeff := findZeroIdx_zero terms idx hidx hzero
      have hih := ih _ _ h
      rw [← evalSum_remove_zero v terms idx hidx hcoeff]; exact hih
    | none =>
      rw [hzero] at h
      cases hpair : VeriPB.findValidCompPairIdx terms degree with
      | some pair =>
        rw [hpair] at h
        obtain ⟨i, j⟩ := pair
        simp only [] at h
        split at h
        · split at h
          · split at h
            · split at h
              · split at h
                · next hi hj hij hlit hle =>
                  have hih := ih _ _ h
                  have hlit_eq := Literal_beq_eq _ _ hlit
                  have hj_eq : terms[j] =
                      (terms[j].1, terms[i].2.negate) :=
                    Prod.ext rfl hlit_eq
                  have hdecomp := list_two_point_decomp
                    terms i j hi hj hij
                  rw [hdecomp, hj_eq]
                  exact cancel_pair_sat_rev v (terms.take i)
                    ((terms.drop (i + 1)).take (j - i - 1))
                    (terms.drop (j + 1)) terms[i].2
                    terms[i].1 terms[j].1 degree hle hih
                · exact h
              · exact h
            · exact h
          · exact h
        · exact h
      | none =>
        rw [hpair] at h
        cases hlike : VeriPB.findLikeTermIdx terms with
        | some pair =>
          rw [hlike] at h
          obtain ⟨i, j⟩ := pair
          simp only [] at h
          split at h
          · split at h
            · split at h
              · split at h
                · next hi hj hij hlit =>
                  have hih := ih _ _ h
                  have hlit_eq := Literal_beq_eq _ _ hlit
                  have hj_eq : terms[j] =
                      (terms[j].1, terms[i].2) :=
                    Prod.ext rfl hlit_eq
                  have hdecomp := list_two_point_decomp
                    terms i j hi hj hij
                  rw [hdecomp, hj_eq]
                  exact merge_terms_sat_rev v (terms.take i)
                    ((terms.drop (i + 1)).take (j - i - 1))
                    (terms.drop (j + 1)) terms[i].2
                    terms[i].1 terms[j].1 degree hih
                · exact h
              · exact h
            · exact h
          · exact h
        | none => rw [hlike] at h; exact h

theorem normalize_sat_rev (c : Constr) (v : Valuation)
    (h : (VeriPB.normalizeConstr c).sat v) : c.sat v := by
  simp only [VeriPB.normalizeConstr, Constr.sat] at *
  exact go_sat_rev _ _ _ v h

private theorem evalSum_perm (v : Valuation) (l1 l2 : List Sat.PB.Term)
    (hp : l1.Perm l2) : Sat.PB.evalSum v l1 = Sat.PB.evalSum v l2 := by
  induction hp with
  | nil => rfl
  | cons x _ ih => simp [Sat.PB.evalSum]; omega
  | swap x y l => simp [Sat.PB.evalSum]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem constrMatchNorm_sat (c1 c2 : Constr) (v : Valuation)
    (h : constrMatchNorm c1 c2 = true) (hsat : c2.sat v) : c1.sat v := by
  unfold constrMatchNorm at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hdeg, _⟩, hterms⟩ := h
  simp only [Constr.sat] at hsat ⊢
  rw [hdeg]
  -- sorted term lists are equal → evalSum is equal
  let cmp := fun (a b : Nat × Sat.PB.Literal) =>
    Sat.PB.Literal.var a.2 < Sat.PB.Literal.var b.2 ||
    (Sat.PB.Literal.var a.2 == Sat.PB.Literal.var b.2 &&
     match a.2, b.2 with | .pos _, .neg _ => true | _, _ => false)
  have hp1 : (c1.terms.mergeSort cmp).Perm c1.terms :=
    List.mergeSort_perm c1.terms cmp
  have hp2 : (c2.terms.mergeSort cmp).Perm c2.terms :=
    List.mergeSort_perm c2.terms cmp
  have heq_sort : c1.terms.mergeSort cmp = c2.terms.mergeSort cmp :=
    hterms
  have h1 := evalSum_perm v _ _ hp1
  have h2 := evalSum_perm v _ _ hp2
  rw [heq_sort] at h1
  omega

/-- If `constrInDB c db = true` and all DB entries are satisfied by `v`,
    then `c` is satisfied by `v`. -/
private theorem constrInDB_sat (c : Constr) (db : Std.HashMap Nat Constr)
    (v : Valuation)
    (h : constrInDB c db = true)
    (hdb : ∀ id c, db.get? id = some c → Constr.sat c v) :
    Constr.sat c v := by
  unfold constrInDB at h
  have hany := List.any_eq_true.mp h
  obtain ⟨⟨id, dbC⟩, hmem, hmatch⟩ := hany
  -- dbC is in the DB and its normalized form matches c's normalized form
  have hget : db.get? id = some dbC := by
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem
  have hdbC_sat := hdb id dbC hget
  -- Chain: dbC.sat v → (normalize dbC).sat v → (normalize c).sat v → c.sat v
  have h1 := normalize_sat dbC v hdbC_sat
  -- hmatch : constrMatchNorm (normalize c) (normalize dbC) = true
  -- constrMatchNorm_sat gives c1.sat from c2.sat, so (normalize c).sat v
  have h2 := constrMatchNorm_sat (VeriPB.normalizeConstr c)
    (VeriPB.normalizeConstr dbC) v hmatch h1
  exact normalize_sat_rev c v h2

-- execPolOps soundness: each pol operation preserves implication

/-- All constraints on a stack are implied by the original formula. -/
def StackSound (original : Array Constr) (_db : Std.HashMap Nat Constr)
    (stack : List VeriPB.StackElem) : Prop :=
  ∀ se ∈ stack, match se with
    | .constr c => ∀ v : Valuation,
        (∀ c' ∈ original.toList, Constr.sat c' v) → Constr.sat c v
    | .nat _ => True

-- StackSound helpers
private theorem StackSound_cons_constr (original : Array Constr)
    (db : Std.HashMap Nat Constr) (c : Constr)
    (stack : List VeriPB.StackElem)
    (hstack : StackSound original db stack)
    (hc : ∀ v : Valuation,
      (∀ c' ∈ original.toList, Constr.sat c' v) → Constr.sat c v) :
    StackSound original db (.constr c :: stack) := by
  intro se hse
  cases hse with
  | head => exact hc
  | tail _ h => exact hstack se h

private theorem StackSound_cons_nat (original : Array Constr)
    (db : Std.HashMap Nat Constr) (n : Nat)
    (stack : List VeriPB.StackElem)
    (hstack : StackSound original db stack) :
    StackSound original db (.nat n :: stack) := by
  intro se hse
  cases hse with
  | head => exact True.intro
  | tail _ h => exact hstack se h

private theorem StackSound_tail (original : Array Constr)
    (db : Std.HashMap Nat Constr) (x : VeriPB.StackElem)
    (stack : List VeriPB.StackElem)
    (h : StackSound original db (x :: stack)) :
    StackSound original db stack :=
  fun se hse => h se (.tail _ hse)

private theorem StackSound_head_constr (original : Array Constr)
    (db : Std.HashMap Nat Constr) (c : Constr)
    (stack : List VeriPB.StackElem)
    (h : StackSound original db (.constr c :: stack)) :
    ∀ v : Valuation,
      (∀ c' ∈ original.toList, Constr.sat c' v) → Constr.sat c v :=
  h (.constr c) (.head _)

/-- Weakening by a variable preserves satisfaction: the removed terms
contribute at most their coefficient sum, which is subtracted from the
degree (truncated). -/
private theorem weakenConstr_sat (c : Constr) (varIdx : Nat) (v : Valuation)
    (hsat : c.sat v) : (VeriPB.weakenConstr c varIdx).sat v := by
  simp only [VeriPB.weakenConstr, Constr.sat] at *
  have h1 : Sat.PB.evalSum v (c.terms.filter fun t => !(t.2.var == varIdx)) +
      Sat.PB.evalSum v (c.terms.filter fun t => t.2.var == varIdx) =
      Sat.PB.evalSum v c.terms :=
    evalSum_filter_add v _ c.terms
  have h2 := evalSum_le_coeffSumR v (c.terms.filter fun t => t.2.var == varIdx)
  omega

/-- The cut operations `k c`, `k n`, `k m` of `execPolOne`: a sound cut `f`
of the normalized top constraint, rejected for `k = 0`. -/
private theorem cut_case (original : Array Constr) (db : Std.HashMap Nat Constr)
    (f : Constr → Nat → Constr)
    (hf : ∀ c k, 0 < k → ∀ v, c.sat v → (f c k).sat v)
    (k : Nat) (c : Constr) (rest stack' : List VeriPB.StackElem)
    (hstack : StackSound original db (.nat k :: .constr c :: rest))
    (hexec : (if k == 0 then none
      else some (VeriPB.StackElem.constr (f (VeriPB.normalizeConstr c) k) :: rest))
        = some stack') :
    StackSound original db stack' := by
  by_cases hk : k == 0
  · simp [hk] at hexec
  · simp only [hk, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hexec
    subst hexec
    have hc := StackSound_head_constr _ _ c rest
      (StackSound_tail _ _ _ _ hstack)
    have hkpos : 0 < k := Nat.pos_of_ne_zero (by simpa using hk)
    exact StackSound_cons_constr _ _ _ rest
      (StackSound_tail _ _ _ _ (StackSound_tail _ _ _ _ hstack))
      fun v hsat => hf _ k hkpos v (normalize_sat c v (hc v hsat))

theorem execPolOne_sound (db : Std.HashMap Nat Constr)
    (original : Array Constr) (stack stack' : List VeriPB.StackElem)
    (op : VeriPB.PolOp)
    (hsound : DBSound original db)
    (hstack : StackSound original db stack)
    (hexec : execPolOne db stack op = some stack') :
    StackSound original db stack' := by
  cases op with
  | pushId id =>
    simp only [execPolOne] at hexec
    match hdb : db[id]? with
    | some c =>
      simp [hdb] at hexec; subst hexec
      exact StackSound_cons_constr _ _ c stack hstack fun v hsat =>
        hsound id c (by rwa [Std.HashMap.get?_eq_getElem?]) v hsat
    | none => simp [hdb] at hexec
  | pushNat n =>
    simp only [execPolOne] at hexec
    injection hexec with hexec; subst hexec
    exact StackSound_cons_nat _ _ n stack hstack
  | pushLitAxiom lit =>
    simp only [execPolOne] at hexec
    match hlit : VeriPB.opbLitToPB lit with
    | .ok pbLit =>
      simp [hlit] at hexec; subst hexec
      exact StackSound_cons_constr _ _ _ stack hstack fun v _ => by
        simp [Constr.sat, Sat.PB.evalSum]
    | .error _ => simp [hlit] at hexec
  | add =>
    simp only [execPolOne] at hexec
    match stack, hstack with
    | .constr c2 :: .constr c1 :: rest, hstack =>
      simp at hexec; subst hexec
      have h1 := StackSound_head_constr _ _ c1 rest
        (StackSound_tail _ _ _ _ hstack)
      have h2 := StackSound_head_constr _ _ c2 _ hstack
      exact StackSound_cons_constr _ _ _ rest
        (StackSound_tail _ _ _ _ (StackSound_tail _ _ _ _ hstack))
        fun v hsat => add_sat c1 c2 v (h1 v hsat) (h2 v hsat)
    | [], _ | [_], _ | .nat _ :: _, _
    | .constr _ :: .nat _ :: _, _ => simp at hexec
  | mul =>
    simp only [execPolOne] at hexec
    match stack, hstack with
    | .nat k :: .constr c :: rest, hstack =>
      simp at hexec; subst hexec
      have hc := StackSound_head_constr _ _ c rest
        (StackSound_tail _ _ _ _ hstack)
      exact StackSound_cons_constr _ _ _ rest
        (StackSound_tail _ _ _ _ (StackSound_tail _ _ _ _ hstack))
        fun v hsat => mul_sat c k v (hc v hsat)
    | [], _ | [_], _ | .constr _ :: _, _
    | .nat _ :: .nat _ :: _, _ => simp at hexec
  | div =>
    simp only [execPolOne] at hexec
    match stack, hstack with
    | .nat k :: .constr c :: rest, hstack =>
      by_cases hk : k == 0
      · simp [hk] at hexec
      · simp [hk] at hexec; subst hexec
        have hc := StackSound_head_constr _ _ c rest
          (StackSound_tail _ _ _ _ hstack)
        have hkpos : 0 < k := by
          simp [beq_iff_eq] at hk; omega
        exact StackSound_cons_constr _ _ _ rest
          (StackSound_tail _ _ _ _ (StackSound_tail _ _ _ _ hstack))
          fun v hsat => div_sat _ k hkpos v
            (normalize_sat c v (hc v hsat))
    | [], _ | [_], _ | .constr _ :: _, _ => simp at hexec
    | .nat _ :: .nat _ :: _, _ => simp at hexec
  | saturate =>
    simp only [execPolOne] at hexec
    match stack, hstack with
    | .constr c :: rest, hstack =>
      simp at hexec; subst hexec
      have hc := StackSound_head_constr _ _ c rest hstack
      exact StackSound_cons_constr _ _ _ rest
        (StackSound_tail _ _ _ _ hstack)
        fun v hsat => saturate_sat _ v (normalize_sat c v (hc v hsat))
    | [], _ | .nat _ :: _, _ => simp at hexec
  | weaken varName =>
    -- Weaken: remove a variable term, reduce degree
    unfold execPolOne at hexec
    match stack, hstack with
    | .constr c :: rest, hstack =>
      have hc := StackSound_head_constr _ _ c rest hstack
      have htail := StackSound_tail _ _ _ _ hstack
      simp only [] at hexec
      split at hexec
      · -- varName.startsWith "x" = true
        split at hexec
        · -- toNat? = some n
          rename_i nVal _
          split at hexec
          · -- nVal > 0
            injection hexec with hexec; subst hexec
            exact StackSound_cons_constr _ _ _ rest htail
              fun v hsat => weakenConstr_sat _ (nVal - 1) v
                (normalize_sat c v (hc v hsat))
          · exact absurd hexec (by simp)
        · exact absurd hexec (by simp)
      · exact absurd hexec (by simp)
    | [], _ | .nat _ :: _, _ => exact absurd hexec (by simp)
  | lowerRhs =>
    simp only [execPolOne] at hexec
    match stack, hstack with
    | .nat k :: .constr c :: rest, hstack =>
      simp at hexec; subst hexec
      have hc := StackSound_head_constr _ _ c rest
        (StackSound_tail _ _ _ _ hstack)
      exact StackSound_cons_constr _ _ _ rest
        (StackSound_tail _ _ _ _ (StackSound_tail _ _ _ _ hstack))
        fun v hsat => by
          have hn := normalize_sat c v (hc v hsat)
          simp only [Constr.sat] at hn ⊢
          omega
    | [], _ | [_], _ | .constr _ :: _, _
    | .nat _ :: .nat _ :: _, _ => simp at hexec
  | divVar =>
    simp only [execPolOne] at hexec
    match stack, hstack with
    | .nat k :: .constr c :: rest, hstack =>
      exact cut_case _ _ _ Sat.PB.cgDiv_sat k c rest _ hstack hexec
    | [], _ | [_], _ | .constr _ :: _, _ => simp at hexec
    | .nat _ :: .nat _ :: _, _ => simp at hexec
  | mir =>
    simp only [execPolOne] at hexec
    match stack, hstack with
    | .nat k :: .constr c :: rest, hstack =>
      exact cut_case _ _ _ Sat.PB.mir_sat k c rest _ hstack hexec
    | [], _ | [_], _ | .constr _ :: _, _ => simp at hexec
    | .nat _ :: .nat _ :: _, _ => simp at hexec
  | mirVar =>
    simp only [execPolOne] at hexec
    match stack, hstack with
    | .nat k :: .constr c :: rest, hstack =>
      exact cut_case _ _ _ Sat.PB.mirVar_sat k c rest _ hstack hexec
    | [], _ | [_], _ | .constr _ :: _, _ => simp at hexec
    | .nat _ :: .nat _ :: _, _ => simp at hexec

theorem execPolOps_sound (db : Std.HashMap Nat Constr)
    (original : Array Constr) (ops : List VeriPB.PolOp)
    (stack stack' : List VeriPB.StackElem)
    (hsound : DBSound original db)
    (hstack : StackSound original db stack)
    (hexec : execPolOps db ops stack = some stack') :
    StackSound original db stack' := by
  induction ops generalizing stack with
  | nil => simp [execPolOps] at hexec; subst hexec; exact hstack
  | cons op rest ih =>
    simp only [execPolOps] at hexec
    match hone : execPolOne db stack op with
    | some s =>
      simp [hone] at hexec
      exact ih s (execPolOne_sound db original stack s op hsound hstack
        hone) hexec
    | none => simp [hone] at hexec

theorem execPolRPNBool_implied (ops : List VeriPB.PolOp)
    (db : Std.HashMap Nat Constr) (original : Array Constr) (c : Constr)
    (hsound : DBSound original db)
    (hpol : execPolRPNBool ops db = some c) :
    ∀ v : Valuation,
      (∀ c' ∈ original.toList, Constr.sat c' v) → Constr.sat c v := by
  simp only [execPolRPNBool] at hpol
  -- execPolOps returns some [.constr c]
  match hexec : execPolOps db ops [] with
  | some [.constr c'] =>
    simp [hexec] at hpol; subst hpol
    have hss : StackSound original db [.constr c'] :=
      execPolOps_sound db original ops [] [.constr c'] hsound
        (fun _ h => nomatch h) hexec
    intro v hsat
    exact hss (.constr c') (List.Mem.head _) v hsat
  | some [] => simp [hexec] at hpol
  | some (.nat _ :: _) => simp [hexec] at hpol
  | some (.constr _ :: _ :: _) => simp [hexec] at hpol
  | none => simp [hexec] at hpol

/-! ### Soundness of RUP propagation -/

/-- A constraint is a consequence of the original formula and the
    negated constraint. -/
def ImpliedByDBAndNeg (original : Array Constr) (_db : Std.HashMap Nat Constr)
    (negConstr c : Constr) : Prop :=
  ∀ v : Valuation, (∀ c' ∈ original.toList, Constr.sat c' v) →
    negConstr.sat v → Constr.sat c v

/-- A partial assignment agrees with a total valuation on every assigned
variable. -/
def Extends (a : PAsgn) (v : Valuation) : Prop :=
  ∀ i b, a.get i = some b → v i = b

/-- An assigned literal evaluates as its assigned value. -/
theorem litValP_some {a : PAsgn} {v : Valuation} (he : Extends a v)
    (l : Sat.PB.Literal) (b : Bool) (h : litValP a l = some b) :
    Sat.PB.evalLit v l = if b then 1 else 0 := by
  cases l with
  | pos i =>
    simp only [litValP] at h
    simp [Sat.PB.evalLit, he i b h]
  | neg i =>
    simp only [litValP] at h
    cases hg : a.get i with
    | none => simp [hg] at h
    | some b' =>
      simp only [hg, Option.map_some, Option.some.injEq] at h
      have := he i b' hg
      subst h; cases b' <;> simp [Sat.PB.evalLit, this]

/-- The active sum bounds the left-hand side of every extending valuation. -/
theorem evalSum_le_activeSum {a : PAsgn} {v : Valuation} (he : Extends a v) :
    ∀ ts : List Sat.PB.Term, Sat.PB.evalSum v ts ≤ activeSum a ts
  | [] => by simp [Sat.PB.evalSum, activeSum]
  | (c, l) :: rest => by
    simp only [Sat.PB.evalSum, activeSum]
    have ih := evalSum_le_activeSum he rest
    have hh : c * Sat.PB.evalLit v l ≤
        (if litValP a l = some false then 0 else c) := by
      split
      · rename_i hf; rw [litValP_some he l false hf]; simp
      · exact Sat.PB.mul_evalLit_le c v l
    omega

/-- A false unassigned term `(c, l)` lowers the left-hand side by `c`
against the active sum. -/
theorem evalSum_add_le_activeSum {a : PAsgn} {v : Valuation} (he : Extends a v)
    (c : Nat) (l : Sat.PB.Literal) (hl : litValP a l = none)
    (hv : Sat.PB.evalLit v l = 0) :
    ∀ ts : List Sat.PB.Term, (c, l) ∈ ts →
      Sat.PB.evalSum v ts + c ≤ activeSum a ts
  | [], hm => nomatch hm
  | (c', l') :: rest, hm => by
    simp only [Sat.PB.evalSum, activeSum]
    rcases List.mem_cons.mp hm with heq | hm'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      have := evalSum_le_activeSum he rest
      simp only [hl, hv]
      simp only [Nat.mul_zero, Nat.zero_add, reduceCtorEq, ↓reduceIte, ge_iff_le]; omega
    · have ih := evalSum_add_le_activeSum he c l hl hv rest hm'
      have hh : c' * Sat.PB.evalLit v l' ≤
          (if litValP a l' = some false then 0 else c') := by
        split
        · rename_i hf; rw [litValP_some he l' false hf]; simp
        · exact Sat.PB.mul_evalLit_le c' v l'
      omega

theorem forcedLits_mem {a : PAsgn} {s : Nat} :
    ∀ {ts : List Sat.PB.Term} {l : Sat.PB.Literal}, l ∈ forcedLits a s ts →
      ∃ c, (c, l) ∈ ts ∧ s < c ∧ litValP a l = none
  | [], _, h => by simp [forcedLits] at h
  | (c, l') :: rest, l, h => by
    simp only [forcedLits] at h
    split at h
    · rename_i hc
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨c, List.mem_cons_self .., hc.1, hc.2⟩
      · obtain ⟨c'', hm, hs, hn⟩ := forcedLits_mem h'
        exact ⟨c'', List.mem_cons_of_mem _ hm, hs, hn⟩
    · obtain ⟨c'', hm, hs, hn⟩ := forcedLits_mem h
      exact ⟨c'', List.mem_cons_of_mem _ hm, hs, hn⟩

/-- Propagating a constraint satisfied by an extending valuation gives no
conflict, and every forced literal is true in the valuation. -/
theorem propagateConstr_sound {a : PAsgn} {v : Valuation} {c : Constr}
    (he : Extends a v) (hc : c.sat v) :
    propagateConstr a c ≠ .conflict ∧
    ∀ ls, propagateConstr a c = .forced ls →
      ∀ l ∈ ls, Sat.PB.evalLit v l = 1 := by
  have hle := evalSum_le_activeSum he c.terms
  simp only [Constr.sat] at hc
  have hnc : ¬ activeSum a c.terms < c.degree := by omega
  simp only [propagateConstr, hnc, if_false]
  constructor
  · split <;> simp
  · intro ls hls l hl
    cases hf : forcedLits a (activeSum a c.terms - c.degree) c.terms with
    | nil => simp [hf] at hls
    | cons l0 ls0 =>
      simp only [hf, PropOutcome.forced.injEq] at hls
      subst hls
      rw [← hf] at hl
      obtain ⟨c', hm, hs, hn⟩ := forcedLits_mem hl
      rcases Sat.PB.evalLit_zero_or_one v l with h0 | h1
      · have := evalSum_add_le_activeSum he c' l hn h0 c.terms hm
        omega
      · exact h1

/-- Making a true literal true keeps the assignment extended by `v`. -/
theorem Extends_setLit {a : PAsgn} {v : Valuation} {l : Sat.PB.Literal}
    (he : Extends a v) (hl : Sat.PB.evalLit v l = 1) : Extends (a.setLit l) v := by
  intro i b h
  simp only [PAsgn.setLit, PAsgn.get, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds] at h
  split at h
  · rename_i hi
    split at h
    · simp only [Option.getD_some, Option.some.injEq] at h
      subst h; subst hi
      cases l with
      | pos j =>
        simp only [Sat.PB.evalLit] at hl
        split at hl <;> simp_all [Sat.PB.Literal.var, litPol]
      | neg j =>
        simp only [Sat.PB.evalLit] at hl
        split at hl <;> simp_all [Sat.PB.Literal.var, litPol]
    · simp at h
  · exact he i b h

theorem assignLits_sound {v : Valuation} :
    ∀ {a : PAsgn} {ls : List Sat.PB.Literal}, Extends a v →
      (∀ l ∈ ls, Sat.PB.evalLit v l = 1) →
      ∃ a', assignLits a ls = some a' ∧ Extends a' v
  | a, [], he, _ => ⟨a, rfl, he⟩
  | a, l :: ls, he, hls => by
    have hl := hls l (List.mem_cons_self ..)
    have hrest := fun l' h => hls l' (List.mem_cons_of_mem _ h)
    simp only [assignLits]
    split
    · exact assignLits_sound he hrest
    · rename_i hf; rw [litValP_some he l false hf] at hl; simp at hl
    · exact assignLits_sound (Extends_setLit he hl) hrest

/-- A round over constraints all satisfied by an extending valuation finds
no conflict and keeps the assignment extended. -/
theorem propagateRound_sound {v : Valuation} :
    ∀ {a : PAsgn} {ch : Bool} {hs : List Constr}, Extends a v →
      (∀ c ∈ hs, c.sat v) →
      ∃ a' ch', propagateRound a ch hs = some (a', ch') ∧ Extends a' v
  | a, ch, [], he, _ => ⟨a, ch, rfl, he⟩
  | a, ch, c :: cs, he, hhs => by
    have hc := hhs c (List.mem_cons_self ..)
    have hcs := fun c' h => hhs c' (List.mem_cons_of_mem _ h)
    obtain ⟨hnc, hforced⟩ := propagateConstr_sound he hc
    simp only [propagateRound]
    split
    · rename_i hcon; exact absurd hcon hnc
    · exact propagateRound_sound he hcs
    · rename_i ls hls
      obtain ⟨a', ha', he'⟩ := assignLits_sound he (hforced ls hls)
      rw [ha']
      exact propagateRound_sound he' hcs

/-- The empty assignment is extended by every valuation. -/
theorem Extends_empty (n : Nat) (v : Valuation) :
    Extends (Array.replicate n none) v := by
  intro i b h
  simp only [PAsgn.get, Array.getElem?_replicate] at h
  split at h <;> simp at h

private theorem resolveHint_implied (negConstr : Constr)
    (db : Std.HashMap Nat Constr) (original : Array Constr)
    (h : VeriPB.RupHint) (rc : Constr)
    (hsound : DBSound original db)
    (hres : resolveHint negConstr db h = some rc) :
    ImpliedByDBAndNeg original db negConstr rc := by
  cases h with
  | negC =>
    simp [resolveHint] at hres; subst hres
    exact fun _ _ hneg => hneg
  | id n =>
    simp [resolveHint] at hres
    exact fun v horiginal _ =>
      hsound n rc (by rwa [Std.HashMap.get?_eq_getElem?]) v horiginal

private theorem resolveHints_implied (negConstr : Constr)
    (db : Std.HashMap Nat Constr) (original : Array Constr)
    (hsound : DBSound original db) :
    ∀ {hints : List VeriPB.RupHint} {cs : List Constr},
      resolveHints negConstr db hints = some cs →
      ∀ c ∈ cs, ImpliedByDBAndNeg original db negConstr c
  | [], cs, h => by
    simp only [resolveHints, Option.some.injEq] at h; subst h
    intro c hc; simp at hc
  | h :: hs, cs, hr => by
    simp only [resolveHints] at hr
    split at hr
    · rename_i c cs' hc hcs
      simp only [Option.some.injEq] at hr; subst hr
      intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hm
      · exact resolveHint_implied negConstr db original h c' hsound hc
      · exact resolveHints_implied negConstr db original hsound hcs c' hm
    · cases hr

/-- A falsified `rup` target satisfies its `rupNegate`. -/
theorem rupNegate_sat_of_not_sat (c : Constr) (v : Valuation)
    (h : ¬ c.sat v) : (rupNegate c).sat v := by
  by_cases hle : (VeriPB.normalizeConstr c).degree ≤ (VeriPB.normalizeConstr c).coeffSum
  · simp only [rupNegate, hle, if_true]
    exact negate_sat_of_not_sat _ v hle fun hs => h (normalize_sat_rev c v hs)
  · simp only [rupNegate, hle, if_false]
    exact Nat.zero_le _

/-- Soundness of `rup`: if the propagation pass over the hint constraints
conflicts, the target is implied by the database: a valuation satisfying the
database but not the target satisfies every hint constraint (the negated
target among them), and propagation never conflicts on constraints that one
valuation satisfies (`propagateRound_sound`). -/
theorem verifyRupBool_implied (negConstr : Constr)
    (hints : List VeriPB.RupHint) (db : Std.HashMap Nat Constr)
    (numVars : Nat) (original : Array Constr) (c : Constr)
    (hsound : DBSound original db)
    (hrup : verifyRupBool negConstr hints db numVars = true)
    (hneg : ∀ v : Valuation, ¬ c.sat v → negConstr.sat v) :
    ∀ v : Valuation,
      (∀ c' ∈ original.toList, Constr.sat c' v) → Constr.sat c v := by
  intro v horiginal
  apply Classical.byContradiction; intro hn
  have hneg_sat : negConstr.sat v := hneg v hn
  simp only [verifyRupBool] at hrup
  split at hrup
  · cases hrup
  · rename_i hs hhs
    have hsat : ∀ c' ∈ hs, c'.sat v := fun c' hc' =>
      resolveHints_implied negConstr db original hsound hhs c' hc'
        v horiginal hneg_sat
    obtain ⟨a', ch', ha', _⟩ :=
      propagateRound_sound (ch := false) (Extends_empty _ v) hsat
    rw [ha'] at hrup
    simp at hrup

-- Main soundness chain

/-- If ¬(c.negate.sat v) and c.degree ≤ c.coeffSum, then c.sat v. -/
private theorem sat_of_not_negate_sat (c : Constr) (v : Valuation)
    (hd : c.degree ≤ c.coeffSum) (h : ¬ c.negate.sat v) : c.sat v :=
  Classical.byContradiction fun hn => h (negate_sat_of_not_sat c v hd hn)

/-- Steps of an array with no forbidden subproof step are all `lstep`s. -/
theorem lsteps_of_not_any (steps : Array VeriPB.ProofStep)
    (h : ¬ steps.any innerStepForbidden = true) :
    ∀ s ∈ steps.toList, isLStep s = true := by
  intro s hs
  cases hc : isLStep s
  · exact absurd (by
      rw [← Array.any_toList]
      exact List.any_eq_true.mpr ⟨s, hs, by simp [innerStepForbidden, hc]⟩) h
  · rfl

theorem DBSatBy_erase_fold (db : Std.HashMap Nat Constr) (ids : List Nat)
    (w : Valuation) (h : DBSatBy db w) :
    DBSatBy (ids.foldl (fun db id => db.erase id) db) w := by
  induction ids generalizing db with
  | nil => exact h
  | cons id _rest ih =>
    apply ih
    intro id' c hget
    exact h id' c (by
      simp only [Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_erase] at hget ⊢
      by_cases heq : id == id'
      · simp [heq] at hget
      · simp [heq] at hget; exact hget)

theorem DBSatBy_insert (db : Std.HashMap Nat Constr) (id : Nat) (c : Constr)
    (w : Valuation) (h : DBSatBy db w) (hc : c.sat w) :
    DBSatBy (db.insert id c) w := by
  intro id' c' hget
  rw [HashMap_get?_insert] at hget
  by_cases heq : id == id'
  · simp [heq] at hget; subst hget; exact hc
  · simp [heq] at hget; exact h id' c' hget

/-! ### Syntactic implication -/

/-- Σ over terms of `f s l`. -/
def tsum (f : Nat → Sat.PB.Literal → Nat) : List Sat.PB.Term → Nat
  | [] => 0
  | (s, l) :: rest => f s l + tsum f rest

private theorem tsum_le_add (f g h : Nat → Sat.PB.Literal → Nat)
    (hle : ∀ s l, f s l ≤ g s l + h s l) :
    ∀ ts : List Sat.PB.Term, tsum f ts ≤ tsum g ts + tsum h ts
  | [] => by simp [tsum]
  | (s, l) :: rest => by
    simp only [tsum]
    have := hle s l
    have := tsum_le_add f g h hle rest
    omega

private theorem tsum_indicator_zero (l0 : Sat.PB.Literal) (c : Nat) :
    ∀ ts : List Sat.PB.Term, l0 ∉ ts.map Prod.snd →
      tsum (fun _ l => if l = l0 then c else 0) ts = 0
  | [] => by simp [tsum]
  | (s, l) :: rest => by
    intro hn
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    simp only [tsum]
    rw [if_neg (fun h => hn.1 h.symm), tsum_indicator_zero l0 c rest hn.2]

private theorem tsum_indicator_le (l0 : Sat.PB.Literal) (c : Nat) :
    ∀ ts : List Sat.PB.Term, (ts.map Prod.snd).Nodup →
      tsum (fun _ l => if l = l0 then c else 0) ts ≤ c
  | [] => by simp [tsum]
  | (s, l) :: rest => by
    intro hnd
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [tsum]
    by_cases hl : l = l0
    · subst hl
      rw [if_pos rfl, tsum_indicator_zero l c rest hnd.1]
      omega
    · rw [if_neg hl]
      have := tsum_indicator_le l0 c rest hnd.2
      omega

private theorem tsum_coeffOf_le (v : Valuation) (S : List Sat.PB.Term)
    (hnd : (S.map Prod.snd).Nodup) :
    ∀ T : List Sat.PB.Term,
      tsum (fun _ l => (coeffOf l T).getD 0 * Sat.PB.evalLit v l) S ≤
        Sat.PB.evalSum v T
  | [] => by
    have hf : (fun (_ : Nat) (l : Sat.PB.Literal) =>
        (coeffOf l []).getD 0 * Sat.PB.evalLit v l) = fun _ _ => 0 := by
      funext _ _; simp [coeffOf]
    have : ∀ ts : List Sat.PB.Term, tsum (fun _ _ => 0) ts = 0 := by
      intro ts; induction ts with
      | nil => rfl
      | cons t rest ih => obtain ⟨s, l⟩ := t; simp [tsum, ih]
    rw [hf, this]; exact Nat.zero_le _
  | (t0, l0) :: T' => by
    have hpt : ∀ (_ : Nat) (l : Sat.PB.Literal),
        (coeffOf l ((t0, l0) :: T')).getD 0 * Sat.PB.evalLit v l ≤
          (if l = l0 then t0 * Sat.PB.evalLit v l0 else 0) +
          (coeffOf l T').getD 0 * Sat.PB.evalLit v l := by
      intro _ l
      simp only [coeffOf]
      by_cases hl : l = l0
      · subst hl; simp
      · have : (l0 == l) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hl h.symm
        simp [this, hl]
    have h1 := tsum_le_add _ _ _ hpt S
    have h2 := tsum_indicator_le l0 (t0 * Sat.PB.evalLit v l0) S hnd
    have h3 := tsum_coeffOf_le v S hnd T'
    simp only [Sat.PB.evalSum]
    omega

private theorem coeffOf_le_evalSum (v : Valuation) (l : Sat.PB.Literal) :
    ∀ (T : List Sat.PB.Term) (t : Nat), coeffOf l T = some t →
      Sat.PB.evalLit v l = 1 → t ≤ Sat.PB.evalSum v T
  | [], _, h, _ => by simp [coeffOf] at h
  | (a, l') :: rest, t, h, hl => by
    simp only [coeffOf] at h
    simp only [Sat.PB.evalSum]
    by_cases heq : l' = l
    · subst heq
      rw [if_pos (beq_self_eq_true l'), Option.some.injEq] at h
      subst h
      rw [hl]; omega
    · have : (l' == l) = false := by simpa using heq
      rw [this] at h
      have := coeffOf_le_evalSum v l rest t h hl
      omega

private theorem evalSum_le_cost (v : Valuation) (T : List Sat.PB.Term) (B : Nat)
    (hT : ∀ l t, coeffOf l T = some t → Sat.PB.evalLit v l = 1 → t < B) :
    ∀ S : List Sat.PB.Term, Sat.PB.evalSum v S ≤ impCostSum T B S +
      tsum (fun _ l => (coeffOf l T).getD 0 * Sat.PB.evalLit v l) S
  | [] => by simp [Sat.PB.evalSum, impCostSum, tsum]
  | (s, l) :: rest => by
    simp only [Sat.PB.evalSum, impCostSum, tsum]
    have ih := evalSum_le_cost v T B hT rest
    have hterm : s * Sat.PB.evalLit v l ≤ impCost T B s l +
        (coeffOf l T).getD 0 * Sat.PB.evalLit v l := by
      unfold impCost
      rcases Sat.PB.evalLit_zero_or_one v l with h0 | h1
      · rw [h0]; simp
      · rw [h1]
        cases hc : coeffOf l T with
        | none => simp
        | some t =>
          have htB := hT l t hc h1
          simp only [Option.getD_some, Nat.mul_one]
          by_cases hts : t < s
          · rw [if_pos ⟨hts, htB⟩]; omega
          · rw [if_neg (fun h => hts h.1)]; omega
    omega

/-- Soundness of the syntactic implication check. -/
theorem impliesSyntactic_sound (S T : Constr) (v : Valuation)
    (h : impliesSyntactic S T = true) (hS : S.sat v) : T.sat v := by
  unfold impliesSyntactic at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with (h0 | hc) | ⟨hnd, hle⟩
  · simp [Constr.sat, h0]
  · exact absurd hS (contra_unsat S v hc)
  · apply Classical.byContradiction
    intro hn
    simp only [Constr.sat] at hn hS ⊢
    have hlt : Sat.PB.evalSum v T.terms < T.degree := by omega
    have hT : ∀ l t, coeffOf l T.terms = some t → Sat.PB.evalLit v l = 1 →
        t < T.degree := fun l t hc hl =>
      Nat.lt_of_le_of_lt (coeffOf_le_evalSum v l T.terms t hc hl) hlt
    have hnd' : (S.terms.map Prod.snd).Nodup := by
      simpa [litsNodup] using hnd
    have h1 := evalSum_le_cost v T.terms T.degree hT S.terms
    have h2 := tsum_coeffOf_le v S.terms hnd' T.terms
    omega

/-- A falsified constraint satisfies its `negTriv`. -/
theorem negTriv_sat_of_not_sat (c : Constr) (v : Valuation) (h : ¬ c.sat v) :
    (negTriv c).sat v := by
  by_cases hle : c.degree ≤ c.coeffSum
  · simp only [negTriv, hle, if_true]
    exact negate_sat_of_not_sat _ v hle h
  · simp only [negTriv, hle, if_false]
    exact Nat.zero_le _

private theorem mem_evalSum_le (v : Valuation) (a : Nat) (l : Sat.PB.Literal) :
    ∀ ts : List Sat.PB.Term, (a, l) ∈ ts →
      a * Sat.PB.evalLit v l ≤ Sat.PB.evalSum v ts
  | [], h => absurd h List.not_mem_nil
  | (b, l') :: rest, h => by
    simp only [Sat.PB.evalSum]
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; omega
    · have := mem_evalSum_le v a l rest h; omega

/-- A goal with a complementary pair whose smaller coefficient reaches the
degree holds for every valuation. -/
theorem trivialByPair_sat (G : Constr) (v : Valuation)
    (h : trivialByPair G = true) : G.sat v := by
  unfold trivialByPair at h
  obtain ⟨⟨a, l⟩, ha, h⟩ := List.any_eq_true.mp h
  obtain ⟨⟨b, l'⟩, hb, h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hl, hd⟩ := h
  subst hl
  simp only [Constr.sat]
  have h1 := mem_evalSum_le v a l G.terms ha
  have h2 := mem_evalSum_le v b l.negate G.terms hb
  have h3 := Sat.PB.evalLit_negate_add v l
  rcases Sat.PB.evalLit_zero_or_one v l with h0 | h1'
  · rw [h0] at h1 h3
    rw [show Sat.PB.evalLit v l.negate = 1 by omega] at h2
    omega
  · rw [h1'] at h1
    omega

/-! ### Redundance goals -/

private theorem evalSum_mono (v w : Valuation) :
    ∀ ts : List Sat.PB.Term,
      (∀ t ∈ ts, Sat.PB.evalLit v t.2 ≤ Sat.PB.evalLit w t.2) →
      Sat.PB.evalSum v ts ≤ Sat.PB.evalSum w ts
  | [] => fun _ => by simp [Sat.PB.evalSum]
  | (a, l) :: rest => fun h => by
    simp only [Sat.PB.evalSum]
    have h1 := h (a, l) (by simp)
    have h2 := evalSum_mono v w rest (fun t ht => h t (by simp [ht]))
    have h3 : a * Sat.PB.evalLit v l ≤ a * Sat.PB.evalLit w l :=
      Nat.mul_le_mul_left a h1
    omega

private theorem litSetTrue_mono (subst : List (Nat × Sat.PB.SubstVal))
    (v : Valuation) (l : Sat.PB.Literal) (h : litSetTrue subst l = true) :
    Sat.PB.evalLit v l ≤ Sat.PB.evalLit (Sat.PB.applyValuation subst v) l := by
  unfold litSetTrue at h
  cases hl : Sat.PB.lookupSubst subst l.var with
  | none =>
    rw [Sat.PB.evalLit_applyValuation_noSubst subst v l hl]
    exact Nat.le_refl _
  | some sv =>
    rw [hl] at h
    cases l with
    | pos i =>
      simp only [Sat.PB.Literal.var] at hl
      cases sv
      · simp at h
      · simp only [Sat.PB.evalLit, Sat.PB.applyValuation, hl, ↓reduceIte]
        split <;> omega
      · simp at h
      · simp at h
    | neg i =>
      simp only [Sat.PB.Literal.var] at hl
      cases sv
      · simp only [Sat.PB.evalLit, Sat.PB.applyValuation, hl, Bool.false_eq_true,
          ↓reduceIte]
        split <;> omega
      · simp at h
      · simp at h
      · simp at h

/-- A witness that sets every touched literal true keeps a constraint
satisfied. -/
theorem touchedSatisfied_sat (subst : List (Nat × Sat.PB.SubstVal))
    (D : Constr) (v : Valuation) (h : touchedSatisfied subst D.terms = true)
    (hD : D.sat v) : D.sat (Sat.PB.applyValuation subst v) := by
  simp only [Constr.sat] at hD ⊢
  have := evalSum_mono v (Sat.PB.applyValuation subst v) D.terms (fun t ht =>
    litSetTrue_mono subst v t.2 (List.all_eq_true.mp h t ht))
  omega

/-- A satisfied normalized goal `D|ω` means `ω(v)` satisfies `D`. -/
theorem substGoal_sat (subst : List (Nat × Sat.PB.SubstVal)) (D : Constr)
    (v : Valuation) (h : (substGoal subst D).sat v) :
    D.sat (Sat.PB.applyValuation subst v) :=
  Sat.PB.applySubstConstr_sat_rev subst D v
    (normalize_sat_rev _ v h)

private theorem evalSum_negate_eq' (v : Valuation) :
    ∀ ts : List Sat.PB.Term,
      Sat.PB.evalSum v (ts.map fun x => (x.1, x.2.negate)) +
        Sat.PB.evalSum v ts = Sat.PB.coeffSumR ts
  | [] => by simp [Sat.PB.evalSum, Sat.PB.coeffSumR]
  | (a, l) :: rest => by
    have ih := evalSum_negate_eq' v rest
    have hmul : a * Sat.PB.evalLit v l.negate + a * Sat.PB.evalLit v l = a := by
      rw [← Nat.mul_add, Sat.PB.evalLit_negate_add' v l, Nat.mul_one]
    simp only [List.map_cons, Sat.PB.evalSum, Sat.PB.coeffSumR]
    omega

/-- A valuation satisfying the objective goal is not improved upon by
applying the witness. -/
theorem objGoalConstr_sound (subst : List (Nat × Sat.PB.SubstVal))
    (obj : Objective) (w : Valuation) (h : (objGoalConstr subst obj).sat w) :
    objVal obj (Sat.PB.applyValuation subst w) ≤ objVal obj w := by
  unfold objGoalConstr at h
  have h' := normalize_sat_rev _ w h
  simp only [Constr.sat, Sat.PB.evalSum_append, Sat.PB.applySubstConstr] at h'
  have hsub := Sat.PB.evalSum_subst subst w
    (obj.map fun x => (x.1, x.2.negate))
  have hneg := evalSum_negate_eq' (Sat.PB.applyValuation subst w) obj
  simp only [objVal]
  omega

/-- A covered database goal holds after applying the witness. -/
theorem dbGoalCovered_sound (subst : List (Nat × Sat.PB.SubstVal))
    (nC : Constr) (goalDb : Std.HashMap Nat Constr)
    (proved : List (String × Constr)) (D : Constr) (w : Valuation)
    (h : dbGoalCovered subst nC goalDb proved D = true)
    (hdb : DBSatBy goalDb w) (hD : D.sat w) (hnC : nC.sat w)
    (hp : ∀ p ∈ proved, p.2.sat w) :
    D.sat (Sat.PB.applyValuation subst w) := by
  unfold dbGoalCovered at h
  simp only [Bool.or_eq_true] at h
  rcases h with htouch | h
  · exact touchedSatisfied_sat subst D w htouch hD
  apply substGoal_sat
  rcases h with ((((htr | himp) | hnimp) | hmatch) | hin)
  · exact trivialByPair_sat _ w htr
  · exact impliesSyntactic_sound _ _ w himp (normalize_sat D w hD)
  · exact impliesSyntactic_sound _ _ w hnimp hnC
  · obtain ⟨p, hpm, hpc⟩ := List.any_eq_true.mp hmatch
    simp only [Bool.and_eq_true] at hpc
    exact constrMatchNorm_sat _ _ w hpc.2 (hp p hpm)
  · exact constrInDB_sat _ goalDb w hin hdb

/-! ### Redundance subproofs -/

/-- The items of a redundance subproof keep a valuation of the subproof
database (top-level steps are `lstep`s, which derive implied constraints or
delete), and every proved goal constraint holds for it (a `proofgoal`
derives a contradiction from the database plus the negated goal). -/
theorem processRedItems_sound
    (execFn : BoolCheckState → List VeriPB.ProofStep → Option BoolCheckState)
    (goalOf : String → Option Constr)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v) :
    ∀ (items : List VeriPB.ProofStep) (st : BoolCheckState)
      (proved : List (String × Constr)) (fin : BoolCheckState)
      (proved' : List (String × Constr)),
      processRedItems execFn goalOf st items proved = some (fin, proved') →
      ∀ v, DBSatBy st.db v → (∀ p ∈ proved, p.2.sat v) →
      DBSatBy fin.db v ∧ ∀ p ∈ proved', p.2.sat v := by
  intro items
  induction items with
  | nil =>
    intro st proved fin proved' h v hv hp
    simp only [processRedItems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hv, hp⟩
  | cons item rest ih =>
    intro st proved fin proved' h v hv hp
    simp only [processRedItems] at h
    split at h
    · -- proofgoal with a closing id
      rename_i gid steps hid
      by_cases hany : steps.any innerStepForbidden = true
      · rw [if_pos hany] at h; cases h
      rw [if_neg hany] at h
      have hls := lsteps_of_not_any steps hany
      cases hG : goalOf gid with
      | none => rw [hG] at h; cases h
      | some G =>
        rw [hG] at h
        simp only [] at h
        cases hx : execFn { st with db := st.db.insert st.nextId (negTriv G), nextId := st.nextId + 1 } steps.toList with
        | none => rw [hx] at h; cases h
        | some fin' =>
          rw [hx] at h
          simp only [] at h
          cases hc : fin'.db[hid]? with
          | none => rw [hc] at h; cases h
          | some c =>
            rw [hc] at h
            simp only [] at h
            by_cases hcon : c.isContra = true
            · rw [if_pos hcon] at h
              have hGv : G.sat v := by
                apply Classical.byContradiction
                intro hn
                have hsub : DBSatBy (st.db.insert st.nextId (negTriv G)) v :=
                  DBSatBy_insert _ _ _ v hv (negTriv_sat_of_not_sat G v hn)
                have hfin := hexec _ fin' steps.toList hls hx v hsub
                exact contra_unsat c v (by simpa [Constr.isContra] using hcon)
                  (hfin hid c (by rwa [Std.HashMap.get?_eq_getElem?]))
              exact ih _ _ fin proved' h v hv (by
                intro p hpm
                simp only [List.mem_cons] at hpm
                rcases hpm with rfl | hpm
                · exact hGv
                · exact hp p hpm)
            · rw [if_neg hcon] at h; cases h
    · -- every other item: an lstep runs at the top level of the subproof
      split at h
      · rename_i hl
        cases hx : execFn st [item] with
        | none => rw [hx] at h; cases h
        | some st' =>
          rw [hx] at h
          simp only [] at h
          exact ih st' proved fin proved' h v
            (hexec st st' [item] (by simpa using hl) hx v hv) hp
      · cases h

/-- Soundness of the redundance check (top-level `red`): a valuation `w`
of the database that falsifies `C` is mapped by the witness to a valuation
that satisfies `C` and the database and has an objective value no larger
than that of `w`. -/
theorem checkRedundance_sound
    (execFn : BoolCheckState → List VeriPB.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (st0 : BoolCheckState) (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List VeriPB.ProofStep) (qedHint : Option Nat) (fid : Nat)
    (h : checkRedundance execFn st0 st0.db subst C items qedHint = some fid)
    (w : Valuation) (hw : DBSatBy st0.db w) (hC : ¬ C.sat w) :
    C.sat (Sat.PB.applyValuation subst w) ∧
      DBSatBy st0.db (Sat.PB.applyValuation subst w) ∧
      objVal st0.objective (Sat.PB.applyValuation subst w) ≤
        objVal st0.objective w := by
  have hnC : (rupNegate C).sat w := rupNegate_sat_of_not_sat C w hC
  have hw1 : DBSatBy (st0.db.insert st0.nextId (rupNegate C)) w :=
    DBSatBy_insert _ _ _ w hw hnC
  unfold checkRedundance at h
  dsimp only at h
  cases hp : processRedItems execFn (redGoalOf subst C st0.objective st0.db) { st0 with db := st0.db.insert st0.nextId (rupNegate C), nextId := st0.nextId + 1 } items [] with
  | none => rw [hp] at h; cases h
  | some r =>
    obtain ⟨fin, proved⟩ := r
    rw [hp] at h
    dsimp only at h
    have ⟨hfin, hproved⟩ := processRedItems_sound execFn _ hexec items _ []
      fin proved hp w hw1 (by simp)
    cases qedHint with
    | some cid =>
      exfalso
      dsimp only at h
      cases hc : fin.db[cid]? with
      | none => simp [hc] at h
      | some c =>
        by_cases hcon : c.isContra = true
        · exact contra_unsat c w (by simpa [Constr.isContra] using hcon)
            (hfin cid c (by rwa [Std.HashMap.get?_eq_getElem?]))
        · simp [hc, hcon] at h
    | none =>
      dsimp only at h
      by_cases hok : (hashGoalsCovered subst C (rupNegate C) st0.objective proved &&
          st0.db.toList.all fun x => dbGoalCovered subst (rupNegate C) st0.db proved x.snd) = true
      · simp only [Bool.and_eq_true] at hok
        obtain ⟨hhash, hall⟩ := hok
        unfold hashGoalsCovered at hhash
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hhash
        obtain ⟨h1, h2⟩ := hhash
        refine ⟨?_, ?_, ?_⟩
        · apply substGoal_sat
          rcases h1 with (htr | hpr) | himp
          · exact trivialByPair_sat _ w htr
          · obtain ⟨p, hpm, hpc⟩ := List.any_eq_true.mp hpr
            simp only [Bool.and_eq_true] at hpc
            exact constrMatchNorm_sat _ _ w hpc.2 (hproved p hpm)
          · exact impliesSyntactic_sound _ _ w himp hnC
        · intro id D hget
          have hmem : (id, D) ∈ st0.db.toList := by
            rw [Std.HashMap.get?_eq_getElem?] at hget
            exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget
          have hcov := List.all_eq_true.mp hall (id, D) hmem
          exact dbGoalCovered_sound subst _ st0.db proved D w hcov hw
            (hw id D hget) hnC hproved
        · rcases h2 with hna | (htr | hpr) | himp
          · show Sat.PB.evalSum _ st0.objective ≤ _
            rw [Sat.PB.evalSum_applyValuation_noSubst subst w _ hna]
            exact Nat.le_refl _
          · exact objGoalConstr_sound subst _ w (trivialByPair_sat _ w htr)
          · obtain ⟨p, hpm, hpc⟩ := List.any_eq_true.mp hpr
            simp only [Bool.and_eq_true] at hpc
            exact objGoalConstr_sound subst _ w
              (constrMatchNorm_sat _ _ w hpc.2 (hproved p hpm))
          · exact objGoalConstr_sound subst _ w
              (impliesSyntactic_sound _ _ w himp hnC)
      · rw [if_neg hok] at h; cases h

/-- `red` step: the formula, objective and best value are unchanged, and
every valuation of the old database has a counterpart in the new one that
is at least as good. -/
theorem redStep_sound
    (execFn : BoolCheckState → List VeriPB.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (state : BoolCheckState) (constr : VeriPB.OPBConstr)
    (substPairs : List (String × String)) (items : List VeriPB.ProofStep)
    (qedHint : Option Nat) (st' : BoolCheckState)
    (h : redStep execFn state constr substPairs items qedHint = some st') :
    st'.origConstrs = state.origConstrs ∧ st'.objective = state.objective ∧
      st'.best = state.best ∧
      ∀ w, DBSatBy state.db w → ∃ w', DBSatBy st'.db w' ∧
        objVal state.objective w' ≤ objVal state.objective w := by
  unfold redStep at h
  split at h
  · cases h
  · rename_i C _
    split at h
    · cases h
    · rename_i subst _
      split at h
      · cases h
      · rename_i fid hchk
        cases h
        refine ⟨rfl, rfl, rfl, fun w hw => ?_⟩
        by_cases hC : C.sat w
        · exact ⟨w, DBSatBy_insert _ _ _ w hw (normalize_sat C w hC),
            Nat.le_refl _⟩
        · obtain ⟨h1, h2, h3⟩ := checkRedundance_sound execFn hexec state
            subst C items qedHint fid hchk w hw hC
          exact ⟨_, DBSatBy_insert _ _ _ _ h2 (normalize_sat C _ h1), h3⟩

/-- Checked deletion erases one id and changes no other field the
invariant depends on (its redundance check is for parity only). -/
theorem delcCheckedStep_spec
    (execFn : BoolCheckState → List VeriPB.ProofStep → Option BoolCheckState)
    (state : BoolCheckState) (ids : List Nat)
    (substPairs : List (String × String))
    (sub : Option (Array VeriPB.ProofStep × Option Nat)) (st' : BoolCheckState)
    (h : delcCheckedStep execFn state ids substPairs sub = some st') :
    st'.origConstrs = state.origConstrs ∧ st'.objective = state.objective ∧
      st'.best = state.best ∧ ∃ did, st'.db = state.db.erase did := by
  unfold delcCheckedStep at h
  dsimp only at h
  split at h
  · rename_i did items qedHint
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · cases h
              exact ⟨rfl, rfl, rfl, did, rfl⟩
  · cases h

/-- Subproof lemma: a sequence of `lstep`s keeps every valuation of the
database (they derive implied constraints or delete). Used for `pbc`
subproofs, `proofgoal` blocks and the top level of redundance subproofs. -/
theorem execStepsFuel_implied : ∀ (fuel : Nat)
    (state state' : BoolCheckState) (steps : List VeriPB.ProofStep),
    (∀ s ∈ steps, isLStep s = true) →
    execStepsFuel fuel state steps = some state' →
    ∀ v, DBSatBy state.db v → DBSatBy state'.db v := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih_fuel =>
    intro state state' steps hls hsteps
    induction steps generalizing state with
    | nil =>
      unfold execStepsFuel at hsteps
      injection hsteps with h; subst h; exact fun _ hv => hv
    | cons step rest ih_rest =>
      have hls_rest : ∀ s ∈ rest, isLStep s = true :=
        fun s hs => hls s (List.mem_cons_of_mem _ hs)
      have hl : isLStep step = true := hls step (by simp)
      have ih_rest := fun st => ih_rest st hls_rest
      unfold execStepsFuel at hsteps
      simp only [] at hsteps
      cases step with
      | pol ops =>
        match hpol : execPolRPNBool ops state.db with
        | some result =>
          simp [hpol] at hsteps
          intro v hv
          apply ih_rest _ hsteps v
          apply DBSatBy_insert _ _ _ v hv
          exact normalize_sat result v
            (execPolRPNBool_implied ops state.db ⟨state.db.toList.map Prod.snd⟩
              result (DBSound_of_toList state.db) hpol v
              (toList_sat_of_DBSat state.db v hv))
        | none => simp [hpol] at hsteps
      | rup constr hints =>
        match hparse : VeriPB.opbConstrToPB constr with
        | .ok pbConstr =>
          simp [hparse] at hsteps
          by_cases hrup : verifyRupBool (rupNegate pbConstr) hints
              state.db state.numVars = false
          · simp [hrup] at hsteps
          · simp [hrup] at hsteps
            have hrup' : verifyRupBool (rupNegate pbConstr) hints
                state.db state.numVars = true := by
              cases h : verifyRupBool (rupNegate pbConstr) hints
                  state.db state.numVars
              · exact absurd h hrup
              · rfl
            intro v hv
            apply ih_rest _ hsteps v
            apply DBSatBy_insert _ _ _ v hv
            exact normalize_sat pbConstr v
              (verifyRupBool_implied (rupNegate pbConstr) hints state.db
                state.numVars ⟨state.db.toList.map Prod.snd⟩ pbConstr
                (DBSound_of_toList state.db) hrup'
                (rupNegate_sat_of_not_sat pbConstr) v
                (toList_sat_of_DBSat state.db v hv))
        | .error _ => simp [hparse] at hsteps
      | ia constr premise =>
        cases premise with
        | none => simp at hsteps
        | some pid =>
          simp only [] at hsteps
          cases hS : state.db[pid]? with
          | none => simp [hS] at hsteps
          | some S =>
            simp only [hS] at hsteps
            cases hparse : VeriPB.opbConstrToPB constr with
            | error _ => simp [hparse] at hsteps
            | ok T0 =>
              simp only [hparse] at hsteps
              by_cases himp : impliesSyntactic (VeriPB.normalizeConstr S)
                  (VeriPB.normalizeConstr T0) = true
              · rw [if_pos himp] at hsteps
                intro v hv
                apply ih_rest _ hsteps v
                apply DBSatBy_insert _ _ _ v hv
                exact impliesSyntactic_sound _ _ v himp
                  (normalize_sat S v (hv pid S
                    (by rwa [Std.HashMap.get?_eq_getElem?])))
              · rw [if_neg himp] at hsteps; simp at hsteps
      | pbc constr innerSteps resultId =>
        by_cases hany : innerSteps.any innerStepForbidden = true
        · simp [hany] at hsteps
        · simp [hany] at hsteps
          match fuel with
          | 0 => simp at hsteps
          | n + 1 =>
            match hparse : VeriPB.opbConstrToPB constr with
            | .ok pbConstr =>
              simp [hparse] at hsteps
              by_cases hcs : pbConstr.degree > pbConstr.coeffSum
              · simp [hcs] at hsteps
              · simp [hcs] at hsteps
                have hcs' : pbConstr.degree ≤ pbConstr.coeffSum :=
                  Nat.le_of_not_lt hcs
                match hinner :
                    execStepsFuel n
                      { state with
                        db := state.db.insert state.nextId pbConstr.negate
                        nextId := state.nextId + 1 }
                      innerSteps.toList with
                | some finalSub =>
                  simp [hinner] at hsteps
                  match hres : finalSub.db[resultId]? with
                  | some c =>
                    simp [hres] at hsteps
                    by_cases hcontra : c.isContra
                    · simp [hcontra] at hsteps
                      intro v hv
                      apply ih_rest _ hsteps v
                      apply DBSatBy_insert _ _ _ v hv
                      apply normalize_sat
                      apply sat_of_not_negate_sat pbConstr v hcs'
                      intro hneg_sat
                      have hfin := ih_fuel n (by omega) _ finalSub
                        innerSteps.toList (lsteps_of_not_any innerSteps hany)
                        hinner v (DBSatBy_insert _ _ _ v hv hneg_sat)
                      exact contra_unsat c v (by
                        simp [Constr.isContra] at hcontra; exact hcontra)
                        (hfin resultId c (by rwa [Std.HashMap.get?_eq_getElem?]))
                    · simp [hcontra] at hsteps
                  | none => simp [hres] at hsteps
                | none => simp [hinner] at hsteps
            | .error _ => simp [hparse] at hsteps
      | deld ids =>
        by_cases hc : ids.any state.coreIds.contains = true
        · simp [hc] at hsteps
        · simp [hc] at hsteps
          intro v hv
          exact ih_rest _ hsteps v (DBSatBy_erase_fold state.db ids v hv)
      | _ => simp [isLStep] at hl


/-! ## Optimization-preserving invariant

The top-level invariant follows VeriPB's semantics for optimization: every
solution of the original formula `F` that improves on the best logged
objective value has a counterpart satisfying the database whose objective
value is at least as good, and the best logged value is the value of an
actual solution of `F`. For a decision instance (no logged solution) this
says: if `F` is satisfiable, so is the database. -/

/-- `v` satisfies every constraint of the formula. -/
def FormulaSat (F : Array Constr) (v : Valuation) : Prop :=
  ∀ c ∈ F.toList, c.sat v

/-- `v` improves on the best logged objective value (vacuous before any
solution is logged). -/
def Improving (obj : Objective) (best : Option Nat) (v : Valuation) : Prop :=
  ∀ b, best = some b → objVal obj v < b

/-- Every improving solution of `F` has a database counterpart that is at
least as good. -/
def DBOpt (F : Array Constr) (obj : Objective) (best : Option Nat)
    (db : Std.HashMap Nat Constr) : Prop :=
  ∀ v, FormulaSat F v → Improving obj best v →
    ∃ w, DBSatBy db w ∧ objVal obj w ≤ objVal obj v

/-- The best logged objective value is attained by a solution of `F`. -/
def BestWitnessed (F : Array Constr) (obj : Objective) (best : Option Nat) :
    Prop :=
  ∀ b, best = some b → ∃ ρ, FormulaSat F ρ ∧ objVal obj ρ = b

/-- The checker's top-level invariant. -/
def StateInv (s : BoolCheckState) : Prop :=
  DBOpt s.origConstrs s.objective s.best s.db ∧
    BestWitnessed s.origConstrs s.objective s.best

theorem DBOpt_insert_dbImplied {F : Array Constr} {obj : Objective}
    {best : Option Nat} {db : Std.HashMap Nat Constr} (id : Nat) (c : Constr)
    (h : DBOpt F obj best db) (himpl : ∀ w, DBSatBy db w → c.sat w) :
    DBOpt F obj best (db.insert id c) := by
  intro v hF himp
  obtain ⟨w, hw, hle⟩ := h v hF himp
  refine ⟨w, fun id' c' hget => ?_, hle⟩
  rw [HashMap_get?_insert] at hget
  by_cases heq : id == id'
  · simp [heq] at hget; subst hget; exact himpl w hw
  · simp [heq] at hget; exact hw id' c' hget

theorem DBOpt_erase_fold {F : Array Constr} {obj : Objective}
    {best : Option Nat} (db : Std.HashMap Nat Constr) (ids : List Nat)
    (h : DBOpt F obj best db) :
    DBOpt F obj best (ids.foldl (fun db id => db.erase id) db) := by
  intro v hF himp
  obtain ⟨w, hw, hle⟩ := h v hF himp
  exact ⟨w, DBSatBy_erase_fold db ids w hw, hle⟩

theorem Improving_updBest (obj : Objective) (best : Option Nat) (b' : Nat)
    (v : Valuation) (h : Improving obj (updBest best b') v) :
    objVal obj v < b' ∧ Improving obj best v := by
  cases best with
  | none =>
    exact ⟨h b' rfl, fun b hb => by cases hb⟩
  | some b =>
    have hmin := h (min b b') rfl
    refine ⟨by omega, fun b0 hb0 => ?_⟩
    cases hb0
    omega

theorem BestWitnessed_updBest (F : Array Constr) (obj : Objective)
    (best : Option Nat) (ρ : Valuation) (hbw : BestWitnessed F obj best)
    (hρ : FormulaSat F ρ) :
    BestWitnessed F obj (updBest best (objVal obj ρ)) := by
  intro b hb
  cases best with
  | none =>
    simp only [updBest, Option.some.injEq] at hb
    exact ⟨ρ, hρ, hb⟩
  | some b0 =>
    simp only [updBest, Option.some.injEq] at hb
    by_cases hle : b0 ≤ objVal obj ρ
    · obtain ⟨ρ0, h0, h0'⟩ := hbw b0 rfl
      exact ⟨ρ0, h0, by omega⟩
    · exact ⟨ρ, hρ, by omega⟩

theorem checkSolution_sound (F : Array Constr) (obj : Objective)
    (lits : List VeriPB.OPBLit) (b' : Nat)
    (h : checkSolution F obj lits = some b') :
    ∃ ρ, FormulaSat F ρ ∧ objVal obj ρ = b' := by
  unfold checkSolution at h
  split at h
  · cases h
  · rename_i pl _
    by_cases hf : formulaSatB F (solValuation pl) = true
    · simp only [hf, ite_true, Option.some.injEq] at h
      refine ⟨solValuation pl, fun c hc => ?_, h⟩
      have hc' := List.all_eq_true.mp hf c hc
      simpa [constrSatB, Constr.sat] using hc'
    · simp [hf] at h

theorem StateInv_init (F : Array Constr) (numVars : Nat) (obj : Objective)
    (offset : Int := 0) :
    StateInv (BoolCheckState.fromConstrs F numVars obj offset) :=
  ⟨fun v hF _ => ⟨v, fun id c hget => hF c (mkDBRec_mem F.toList 1 id c hget),
    Nat.le_refl _⟩,
   fun b hb => by simp [BoolCheckState.fromConstrs] at hb⟩

/-- Main step lemma with field preservation: execution preserves the
optimization invariant and never changes the formula or the objective. -/
theorem execStepsFuel_inv_preserve_fields : ∀ (fuel : Nat)
    (state state' : BoolCheckState) (steps : List VeriPB.ProofStep),
    StateInv state →
    execStepsFuel fuel state steps = some state' →
    StateInv state' ∧ state'.origConstrs = state.origConstrs ∧
      state'.objective = state.objective := by
  intro fuel state state' steps hinv hsteps
  induction steps generalizing state with
  | nil =>
    unfold execStepsFuel at hsteps
    injection hsteps with h; subst h; exact ⟨hinv, rfl, rfl⟩
  | cons step rest ih_rest =>
    unfold execStepsFuel at hsteps
    simp only [] at hsteps
    -- a step that keeps formula, objective and best value and maps every
    -- valuation of the database to an at least as good one
    have hstep : ∀ st : BoolCheckState,
        st.origConstrs = state.origConstrs → st.objective = state.objective →
        st.best = state.best →
        (∀ w, DBSatBy state.db w → ∃ w', DBSatBy st.db w' ∧
          objVal state.objective w' ≤ objVal state.objective w) →
        execStepsFuel fuel st rest = some state' →
        StateInv state' ∧ state'.origConstrs = state.origConstrs ∧
          state'.objective = state.objective := by
      intro st hF hO hB hdb hrest
      have hinv' : StateInv st := by
        refine ⟨fun v hFv himp => ?_, ?_⟩
        · rw [hF, hO, hB] at *
          obtain ⟨w, hw, hle⟩ := hinv.1 v hFv himp
          obtain ⟨w', hw', hle'⟩ := hdb w hw
          exact ⟨w', hw', Nat.le_trans hle' hle⟩
        · rw [hF, hO, hB]; exact hinv.2
      obtain ⟨h1, h2, h3⟩ := ih_rest st hinv' hrest
      exact ⟨h1, h2.trans hF, h3.trans hO⟩
    cases step with
    | formulaSize n =>
      by_cases hfs : state.formulaSize != n
      · simp [hfs] at hsteps
      · simp [hfs] at hsteps; exact ih_rest state hinv hsteps
    | pol ops =>
      match hpol : execPolRPNBool ops state.db with
      | some result =>
        simp [hpol] at hsteps
        apply ih_rest _ _ hsteps
        refine ⟨DBOpt_insert_dbImplied state.nextId _ hinv.1 ?_, hinv.2⟩
        intro v hdb
        exact normalize_sat result v
          (execPolRPNBool_implied ops state.db ⟨state.db.toList.map Prod.snd⟩
            result (DBSound_of_toList state.db) hpol v
            (toList_sat_of_DBSat state.db v hdb))
      | none => simp [hpol] at hsteps
    | rup constr hints =>
      match hparse : VeriPB.opbConstrToPB constr with
      | .ok pbConstr =>
        simp [hparse] at hsteps
        by_cases hrup : verifyRupBool (rupNegate pbConstr) hints
            state.db state.numVars = false
        · simp [hrup] at hsteps
        · simp [hrup] at hsteps
          have hrup' : verifyRupBool (rupNegate pbConstr) hints
              state.db state.numVars = true := by
            cases h : verifyRupBool (rupNegate pbConstr) hints
                state.db state.numVars
            · exact absurd h hrup
            · rfl
          apply ih_rest _ _ hsteps
          refine ⟨DBOpt_insert_dbImplied state.nextId _ hinv.1 ?_, hinv.2⟩
          intro v hdb
          exact normalize_sat pbConstr v
            (verifyRupBool_implied (rupNegate pbConstr) hints state.db
              state.numVars ⟨state.db.toList.map Prod.snd⟩ pbConstr
              (DBSound_of_toList state.db) hrup'
              (rupNegate_sat_of_not_sat pbConstr) v
              (toList_sat_of_DBSat state.db v hdb))
      | .error _ => simp [hparse] at hsteps
    | ia constr premise =>
      cases premise with
      | none => simp at hsteps
      | some pid =>
        simp only [] at hsteps
        cases hS : state.db[pid]? with
        | none => simp [hS] at hsteps
        | some S =>
          simp only [hS] at hsteps
          cases hparse : VeriPB.opbConstrToPB constr with
          | error _ => simp [hparse] at hsteps
          | ok T0 =>
            simp only [hparse] at hsteps
            by_cases himp : impliesSyntactic (VeriPB.normalizeConstr S)
                (VeriPB.normalizeConstr T0) = true
            · rw [if_pos himp] at hsteps
              apply ih_rest _ _ hsteps
              refine ⟨DBOpt_insert_dbImplied state.nextId _ hinv.1 ?_, hinv.2⟩
              intro v hdb
              exact impliesSyntactic_sound _ _ v himp
                (normalize_sat S v (hdb pid S
                  (by rwa [Std.HashMap.get?_eq_getElem?])))
            · rw [if_neg himp] at hsteps; simp at hsteps
    | pbc constr innerSteps resultId =>
      by_cases hany : innerSteps.any innerStepForbidden = true
      · simp [hany] at hsteps
      · simp [hany] at hsteps
        match fuel with
        | 0 => simp at hsteps
        | n + 1 =>
          match hparse : VeriPB.opbConstrToPB constr with
          | .ok pbConstr =>
            simp [hparse] at hsteps
            by_cases hcs : pbConstr.degree > pbConstr.coeffSum
            · simp [hcs] at hsteps
            · simp [hcs] at hsteps
              have hcs' : pbConstr.degree ≤ pbConstr.coeffSum :=
                Nat.le_of_not_lt hcs
              match hinner :
                  execStepsFuel n
                    { state with
                      db := state.db.insert state.nextId pbConstr.negate
                      nextId := state.nextId + 1 }
                    innerSteps.toList with
              | some finalSub =>
                simp [hinner] at hsteps
                match hres : finalSub.db[resultId]? with
                | some c =>
                  simp [hres] at hsteps
                  by_cases hcontra : c.isContra
                  · simp [hcontra] at hsteps
                    apply ih_rest _ _ hsteps
                    refine ⟨DBOpt_insert_dbImplied finalSub.nextId _ hinv.1 ?_,
                      hinv.2⟩
                    intro v hdb
                    apply normalize_sat
                    apply sat_of_not_negate_sat pbConstr v hcs'
                    intro hneg_sat
                    have hfin := execStepsFuel_implied n _ finalSub
                      innerSteps.toList (lsteps_of_not_any innerSteps hany)
                      hinner v (DBSatBy_insert _ _ _ v hdb hneg_sat)
                    exact contra_unsat c v (by
                      simp [Constr.isContra] at hcontra; exact hcontra)
                      (hfin resultId c (by rwa [Std.HashMap.get?_eq_getElem?]))
                  · simp [hcontra] at hsteps
                | none => simp [hres] at hsteps
              | none => simp [hinner] at hsteps
          | .error _ => simp [hparse] at hsteps
    | red constr substPairs goals =>
      match fuel with
      | 0 => simp at hsteps
      | n + 1 =>
        simp only [] at hsteps
        cases hr : redStep (execStepsFuel n) state constr substPairs
            (goalsToItems goals) none with
        | none => rw [hr] at hsteps; simp at hsteps
        | some st =>
          rw [hr] at hsteps
          obtain ⟨hF, hO, hB, hdb⟩ := redStep_sound (execStepsFuel n)
            (fun st st' steps hls hex v hv =>
              execStepsFuel_implied n st st' steps hls hex v hv)
            state constr substPairs _ none st hr
          exact hstep st hF hO hB hdb hsteps
    | strengthening rule constr substPairs items qedHint =>
      cases rule with
      | dom => simp at hsteps
      | red =>
        match fuel with
        | 0 => simp at hsteps
        | n + 1 =>
          simp only [] at hsteps
          cases hr : redStep (execStepsFuel n) state constr substPairs
              items.toList qedHint with
          | none => rw [hr] at hsteps; simp at hsteps
          | some st =>
            rw [hr] at hsteps
            obtain ⟨hF, hO, hB, hdb⟩ := redStep_sound (execStepsFuel n)
              (fun st st' steps hls hex v hv =>
                execStepsFuel_implied n st st' steps hls hex v hv)
              state constr substPairs _ qedHint st hr
            exact hstep st hF hO hB hdb hsteps
    | delcChecked ids substPairs sub =>
      match fuel with
      | 0 => simp at hsteps
      | n + 1 =>
        simp only [] at hsteps
        cases hd : delcCheckedStep (execStepsFuel n) state ids substPairs sub with
        | none => rw [hd] at hsteps; simp at hsteps
        | some st =>
          rw [hd] at hsteps
          obtain ⟨hF, hO, hB, did, hdb⟩ := delcCheckedStep_spec _ state ids
            substPairs sub st hd
          exact hstep st hF hO hB (fun w hw => ⟨w, by
            rw [hdb]
            exact DBSatBy_erase_fold state.db [did] w hw, Nat.le_refl _⟩) hsteps
    | deld ids =>
      by_cases hc : ids.any state.coreIds.contains = true
      · simp [hc] at hsteps
      · simp [hc] at hsteps
        apply ih_rest _ _ hsteps
        exact ⟨DBOpt_erase_fold state.db ids hinv.1, hinv.2⟩
    | delc ids =>
      by_cases hc : (state.s2c && !allCore state) = true
      · simp only [hc, if_true] at hsteps; simp at hsteps
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hsteps
        apply ih_rest _ _ hsteps
        exact ⟨DBOpt_erase_fold state.db ids hinv.1, hinv.2⟩
    | core ids =>
      by_cases hc : ids.all state.db.contains = true
      · simp only [hc, if_true] at hsteps
        apply ih_rest _ _ hsteps; exact hinv
      · simp [hc] at hsteps
    | coreRange lo hi => apply ih_rest _ _ hsteps; exact hinv
    | strengtheningToCore on =>
      cases on <;> (apply ih_rest _ _ hsteps; exact hinv)
    | loadOrder name _ =>
      cases name
      · exact ih_rest state hinv hsteps
      · simp at hsteps
    | defOrder _ => apply ih_rest _ _ hsteps; exact hinv
    | output => exact ih_rest state hinv hsteps
    | conclusionNone => exact ih_rest state hinv hsteps
    | conclusion id =>
      match hdb : state.db[id]? with
      | some c =>
        simp [hdb] at hsteps
        by_cases hc : c.isContra
        · simp [hc] at hsteps; exact ih_rest state hinv hsteps
        · simp [hc] at hsteps
      | none => simp [hdb] at hsteps
    | sol lits value =>
      match hchk : checkSolution state.origConstrs state.objective lits with
      | none => simp [hchk] at hsteps
      | some b' =>
        by_cases hv : solValueOk state.offset b' value = false
        · simp [hchk, hv] at hsteps
        simp [hchk, hv] at hsteps
        apply ih_rest _ _ hsteps
        obtain ⟨ρ, hρ, hval⟩ := checkSolution_sound _ _ _ _ hchk
        have hbw := BestWitnessed_updBest _ _ _ ρ hinv.2 hρ
        rw [hval] at hbw
        exact ⟨fun v hF himp =>
          hinv.1 v hF (Improving_updBest _ _ _ _ himp).2, hbw⟩
    | soli lits value =>
      match hchk : checkSolution state.origConstrs state.objective lits with
      | none => simp [hchk] at hsteps
      | some b' =>
        by_cases hv : solValueOk state.offset b' value = false
        · simp [hchk, hv] at hsteps
        simp [hchk, hv] at hsteps
        apply ih_rest _ _ hsteps
        obtain ⟨ρ, hρ, hval⟩ := checkSolution_sound _ _ _ _ hchk
        have hbw := BestWitnessed_updBest _ _ _ ρ hinv.2 hρ
        rw [hval] at hbw
        refine ⟨fun v hF himp => ?_, hbw⟩
        obtain ⟨hlt, himp0⟩ := Improving_updBest _ _ _ _ himp
        obtain ⟨w, hw, hle⟩ := hinv.1 v hF himp0
        refine ⟨w, fun id' c' hget => ?_, hle⟩
        rw [HashMap_get?_insert] at hget
        by_cases heq : state.nextId == id'
        · simp [heq] at hget; subst hget
          -- w satisfies the improvement constraint: objVal w ≤ objVal v < b'
          apply negate_sat_of_not_sat
          · show b' ≤ Sat.PB.coeffSumR state.objective
            rw [← hval]
            exact Sat.PB.evalSum_le_coeffSumR ρ state.objective
          · intro hs
            simp only [Constr.sat] at hs
            simp only [objVal] at hle hlt
            omega
        · simp [heq] at hget; exact hw id' c' hget
    | conclusionSat _ => exact ih_rest state hinv hsteps
    | conclusionBounds _ _ _ _ => exact ih_rest state hinv hsteps
    | _ => simp at hsteps

/-- Main step lemma: execution preserves the optimization invariant. -/
theorem execStepsFuel_inv_preserve (fuel : Nat)
    (state state' : BoolCheckState) (steps : List VeriPB.ProofStep)
    (hinv : StateInv state)
    (hsteps : execStepsFuel fuel state steps = some state') :
    StateInv state' :=
  (execStepsFuel_inv_preserve_fields fuel state state' steps hinv hsteps).1

/-- Execution from the initial state of `F` and `obj`, ending with a
contradiction in the database, proves that no solution of `F` improves on
the best logged objective value. With no logged solution (`best = none`),
`F` is unsatisfiable. -/
theorem execStepsFuel_no_improving (fuel : Nat) (F : Array Constr)
    (numVars : Nat) (obj : Objective) (steps : List VeriPB.ProofStep)
    (s : BoolCheckState)
    (hexec : execStepsFuel fuel (BoolCheckState.fromConstrs F numVars obj)
      steps = some s)
    (id : Nat) (c : Constr) (hc : s.db.get? id = some c)
    (hcontra : c.isContra = true) :
    (∀ v, FormulaSat F v → ¬ Improving obj s.best v) ∧
      BestWitnessed F obj s.best := by
  obtain ⟨hinv, hF, hO⟩ := execStepsFuel_inv_preserve_fields fuel _ s steps
    (StateInv_init F numVars obj) hexec
  have hF' : s.origConstrs = F := hF
  have hO' : s.objective = obj := hO
  obtain ⟨hdbopt, hbw⟩ := hinv
  rw [hF', hO'] at hdbopt hbw
  refine ⟨fun v hv himp => ?_, hbw⟩
  obtain ⟨w, hw, _⟩ := hdbopt v hv himp
  exact contra_unsat c w (by simpa [Constr.isContra] using hcontra) (hw id c hc)

/-- Bounds corollary: a contradiction in the final database with best
logged value `b` proves that `b` is the optimum: every solution of `F` has
objective value at least `b`, and some solution attains `b`. The objective
value is `objVal obj`, the normalized objective without its constant offset
(negative coefficients are rewritten on negated literals and the offset is
dropped), not the value of the OPB `min:` line itself. -/
theorem execStepsFuel_bounds (fuel : Nat) (F : Array Constr) (numVars : Nat)
    (obj : Objective) (steps : List VeriPB.ProofStep) (s : BoolCheckState)
    (hexec : execStepsFuel fuel (BoolCheckState.fromConstrs F numVars obj)
      steps = some s)
    (id : Nat) (c : Constr) (hc : s.db.get? id = some c)
    (hcontra : c.isContra = true) (b : Nat) (hb : s.best = some b) :
    (∀ v, FormulaSat F v → b ≤ objVal obj v) ∧
      (∃ ρ, FormulaSat F ρ ∧ objVal obj ρ = b) := by
  obtain ⟨hno, hbw⟩ := execStepsFuel_no_improving fuel F numVars obj steps s
    hexec id c hc hcontra
  refine ⟨fun v hv => Nat.le_of_not_lt fun hlt => hno v hv ?_, hbw b hb⟩
  intro b' hb'
  rw [hb] at hb'
  cases hb'
  exact hlt

theorem checkProof_sound (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (names : List (String × Nat)) (proofStr : String)
    (h : checkProofBool constrs numVars objective names proofStr = true) :
    formulaUnsat constrs := by
  unfold checkProofBool at h
  match hparse : VeriPB.parseVeriPBProofWith
      (VeriPB.VarTable.ofList names numVars) proofStr with
  | .error _ => simp [hparse] at h
  | .ok proofData =>
    simp only [hparse] at h
    match hexec : execStepsFuel (pbcDepth proofData.steps.toList + 1)
        (BoolCheckState.fromConstrs constrs (max numVars proofData.numVars)
          objective)
        proofData.steps.toList with
    | some finalState =>
      simp only [hexec] at h
      -- Extract conclusion information
      simp only [hasUnsatConclusion, Bool.and_eq_true] at h
      obtain ⟨hbest, hpi⟩ := h
      have hbn : finalState.best = none := Option.isNone_iff_eq_none.mp hbest
      -- the placed conclusion is `conclusion UNSAT : id` with `db[id]`
      -- contradictory
      split at hpi
      · rename_i id _
        split at hpi
        · rename_i c hdb
          have hno := (execStepsFuel_no_improving _ constrs _ objective
            _ finalState hexec id c (by rwa [Std.HashMap.get?_eq_getElem?])
            (by simpa [Constr.isContra] using hpi)).1
          intro v
          exact Classical.byContradiction fun hne => by
            have hall : FormulaSat constrs v :=
              fun c' hc' => Classical.byContradiction fun hn =>
                hne ⟨c', hc', hn⟩
            exact hno v hall (fun b hb => by rw [hbn] at hb; cases hb)
        · exact absurd hpi Bool.false_ne_true
      · exact absurd hpi Bool.false_ne_true
    | none => simp [hexec] at h

/-! ## SAT and BOUNDS conclusions

The statements are about the normalized objective in minimization form: the
value of `v` is `objVal obj v + offset` (`Int`), where `obj` are the
normalized nonnegative terms and `offset` the constant
(`VeriPB.OPBObjective`). For `max: f` the parser negates the objective, as
VeriPB does, so the statements are about `−f`: a lower bound `lb` gives
`f ≤ −lb` for every solution, an upper bound `ub` a solution with
`f ≥ −ub`. -/

/-- `F` has a solution. -/
def formulaSatisfiable (F : Array Constr) : Prop := ∃ v, FormulaSat F v

/-- Lower bound on the normalized min-form objective `objVal obj v + offset`
over the solutions of `F`; `none` (`INF`) means that `F` has no solution.
For `max: f` (negated by the parser) `some lb` gives `f ≤ −lb` for every
solution. -/
def formulaLowerBound (F : Array Constr) (obj : Objective) (offset : Int) :
    Option Int → Prop
  | none => ∀ v, ¬ FormulaSat F v
  | some lb => ∀ v, FormulaSat F v → lb ≤ (objVal obj v : Int) + offset

/-- Upper bound: some solution of `F` has normalized min-form objective value
`objVal obj v + offset` at most `ub`; `none` (`INF`) claims nothing. For
`max: f` (negated by the parser) `some ub` gives a solution with
`f ≥ −ub`. -/
def formulaUpperBound (F : Array Constr) (obj : Objective) (offset : Int) :
    Option Int → Prop
  | none => True
  | some ub => ∃ v, FormulaSat F v ∧ (objVal obj v : Int) + offset ≤ ub

/-- `conclusion BOUNDS lb ub` (CakePB's `sem_concl` for `OBounds`): bounds on
the normalized min-form objective `objVal obj v + offset`. For `max: f`
(negated by the parser) the statement is about `−f`: `lb` gives `f ≤ −lb`
for every solution and `ub` a solution with `f ≥ −ub`. -/
def formulaBounds (F : Array Constr) (obj : Objective) (offset : Int)
    (lb ub : Option Int) : Prop :=
  formulaLowerBound F obj offset lb ∧ formulaUpperBound F obj offset ub

/-- Meaning of a claim. -/
def Claim.holds (F : Array Constr) (obj : Objective) (offset : Int) :
    Claim → Prop
  | .unsat => formulaUnsat F
  | .sat => formulaSatisfiable F
  | .bounds lb ub => formulaBounds F obj offset lb ub

/-- Equal lower and upper bounds: `k` is the optimum, attained by a
solution. -/
theorem formulaBounds_optimum {F : Array Constr} {obj : Objective}
    {offset k : Int} (h : formulaBounds F obj offset (some k) (some k)) :
    (∃ v, FormulaSat F v ∧ (objVal obj v : Int) + offset = k) ∧
      ∀ v, FormulaSat F v → k ≤ (objVal obj v : Int) + offset := by
  simp only [formulaBounds, formulaLowerBound, formulaUpperBound] at h
  obtain ⟨hlb, v, hv, hle⟩ := h
  exact ⟨⟨v, hv, Int.le_antisymm hle (hlb v hv)⟩, hlb⟩

theorem formulaUnsat_of_forall {F : Array Constr}
    (h : ∀ v, ¬ FormulaSat F v) : formulaUnsat F := by
  intro v
  exact Classical.byContradiction fun hne =>
    h v fun c hc => Classical.byContradiction fun hn => hne ⟨c, hc, hn⟩

/-- A contradiction with no logged solution: `F` has no solution. -/
theorem StateInv_unsat {s : BoolCheckState} (hinv : StateInv s)
    (hb : s.best = none) {id : Nat} {c : Constr} (hc : s.db[id]? = some c)
    (hcontra : c.isContra = true) : ∀ v, ¬ FormulaSat s.origConstrs v := by
  intro v hv
  obtain ⟨w, hw, _⟩ := hinv.1 v hv (fun b hb' => by rw [hb] at hb'; cases hb')
  exact contra_unsat c w (by simpa [Constr.isContra] using hcontra)
    (hw id c (by rw [Std.HashMap.get?_eq_getElem?]; exact hc))

/-- A database constraint implying `objective ≥ lb − offset`, with `lb` at
most the best logged value: `lb` is a lower bound. Improving solutions have
a database counterpart (`DBOpt`) that satisfies the implied bound; the
others are bounded by the best value. -/
theorem StateInv_lower {s : BoolCheckState} (hinv : StateInv s) (offset : Int)
    {id : Nat} {D : Constr} (hD : s.db[id]? = some D) (l : Int)
    (hbest : ∀ b, s.best = some b → l ≤ (b : Int) + offset)
    (himpl : impliesSyntactic (VeriPB.normalizeConstr D)
      (VeriPB.normalizeConstr (lowerBoundConstr s.objective offset l)) = true) :
    ∀ v, FormulaSat s.origConstrs v →
      l ≤ (objVal s.objective v : Int) + offset := by
  intro v hv
  by_cases himp : Improving s.objective s.best v
  · obtain ⟨w, hw, hle⟩ := hinv.1 v hv himp
    have hDw : D.sat w := hw id D (by rw [Std.HashMap.get?_eq_getElem?]; exact hD)
    have hT := normalize_sat_rev _ w
      (impliesSyntactic_sound _ _ w himpl (normalize_sat D w hDw))
    simp only [lowerBoundConstr, Constr.sat] at hT
    simp only [objVal] at hle ⊢
    have := Int.self_le_toNat (l - offset)
    have : (((l - offset).toNat : Nat) : Int) ≤ (Sat.PB.evalSum w s.objective : Int) :=
      Int.ofNat_le.mpr hT
    have : (Sat.PB.evalSum w s.objective : Int) ≤ (Sat.PB.evalSum v s.objective : Int) :=
      Int.ofNat_le.mpr hle
    omega
  · simp only [Improving, Classical.not_forall] at himp
    obtain ⟨b, hb, hnlt⟩ := himp
    have := hbest b hb
    have : (b : Int) ≤ (objVal s.objective v : Int) :=
      Int.ofNat_le.mpr (Nat.le_of_not_lt hnlt)
    omega

theorem lowerBoundOk_sound {s : BoolCheckState} (hinv : StateInv s)
    (offset : Int) (lb : Option Int) (hint : Option Nat)
    (h : lowerBoundOk (fun id => s.db[id]?) s.objective offset s.best lb hint
      = true) :
    formulaLowerBound s.origConstrs s.objective offset lb := by
  cases hint with
  | none => simp [lowerBoundOk] at h
  | some id =>
    cases hD : s.db[id]? with
    | none => simp [lowerBoundOk, hD] at h
    | some D =>
      cases lb with
      | none =>
        simp only [lowerBoundOk, hD, Bool.and_eq_true] at h
        obtain ⟨hb, hc⟩ := h
        exact StateInv_unsat hinv (Option.isNone_iff_eq_none.mp hb) hD hc
      | some l =>
        simp only [lowerBoundOk, hD, Bool.and_eq_true] at h
        obtain ⟨hb, himpl⟩ := h
        refine StateInv_lower hinv offset hD l (fun b hb' => ?_) himpl
        rw [hb'] at hb
        simpa using hb

theorem upperBoundOk_sound (F : Array Constr) (obj : Objective)
    (offset : Int) (best : Option Nat) (ub : Option Int)
    (lits : Option (List VeriPB.OPBLit)) (hbw : BestWitnessed F obj best)
    (h : upperBoundOk F obj offset best ub lits = true) :
    formulaUpperBound F obj offset ub := by
  cases ub with
  | none => trivial
  | some u =>
    simp only [formulaUpperBound]
    cases lits with
    | none =>
      cases hb : best with
      | none => simp [upperBoundOk, hb] at h
      | some b =>
        simp only [upperBoundOk, hb, decide_eq_true_eq] at h
        obtain ⟨ρ, hρ, hval⟩ := hbw b hb
        exact ⟨ρ, hρ, by rw [hval]; exact h⟩
    | some ls =>
      cases hc : checkSolution F obj ls with
      | none => simp [upperBoundOk, hc] at h
      | some val =>
        simp only [upperBoundOk, hc, decide_eq_true_eq] at h
        obtain ⟨ρ, hρ, hval⟩ := checkSolution_sound F obj ls val hc
        exact ⟨ρ, hρ, by rw [hval]; exact h⟩

/-- Soundness of the conclusion evaluation on a state satisfying the
invariant. -/
theorem conclusionClaim_sound (s : BoolCheckState) (hinv : StateInv s)
    (offset : Int) (step : VeriPB.ProofStep) (claim : Claim)
    (h : conclusionClaim (fun id => s.db[id]?) s.origConstrs s.objective
      offset s.best step = some claim) :
    claim.holds s.origConstrs s.objective offset := by
  cases step with
  | conclusion id =>
    cases hc : s.db[id]? with
    | none => simp [conclusionClaim, hc] at h
    | some c =>
      by_cases hcon : c.isContra = true
      · cases hb : s.best with
        | none =>
          simp only [conclusionClaim, hc, hcon, hb, if_true,
            Option.some.injEq] at h
          subst h
          exact formulaUnsat_of_forall (StateInv_unsat hinv hb hc hcon)
        | some b => simp [conclusionClaim, hc, hcon, hb] at h
      · simp [conclusionClaim, hc, hcon] at h
  | conclusionSat lits =>
    by_cases hs : satOk s.origConstrs s.objective s.best lits = true
    · simp only [conclusionClaim, hs, if_true, Option.some.injEq] at h
      subst h
      simp only [Claim.holds, formulaSatisfiable]
      cases lits with
      | none =>
        simp only [satOk] at hs
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨ρ, hρ, _⟩ := hinv.2 b hb
        exact ⟨ρ, hρ⟩
      | some ls =>
        simp only [satOk] at hs
        obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨ρ, hρ, _⟩ := checkSolution_sound _ _ ls val hval
        exact ⟨ρ, hρ⟩
    · simp [conclusionClaim, hs] at h
  | conclusionBounds lb hint ub lits =>
    by_cases hok : (lowerBoundOk (fun id => s.db[id]?) s.objective offset
        s.best (boundOpt lb) hint &&
        upperBoundOk s.origConstrs s.objective offset s.best (boundOpt ub)
          lits) = true
    · simp only [conclusionClaim] at h
      rw [if_pos hok, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hok
      exact ⟨lowerBoundOk_sound hinv offset _ hint hok.1,
        upperBoundOk_sound _ _ offset _ _ lits hinv.2 hok.2⟩
    · simp only [conclusionClaim] at h
      rw [if_neg hok] at h
      cases h
  | _ => simp [conclusionClaim] at h

/-- Soundness of `proofClaim?`: the claimed result holds for the formula
and the OPB objective `objVal objective + offset`. -/
theorem proofClaim?_sound (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (offset : Int) (names : List (String × Nat))
    (proofStr : String) (claim : Claim)
    (h : proofClaim? constrs numVars objective offset names proofStr =
      some claim) :
    claim.holds constrs objective offset := by
  unfold proofClaim? at h
  match hparse : VeriPB.parseVeriPBProofWith
      (VeriPB.VarTable.ofList names numVars) proofStr with
  | .error _ => simp [hparse] at h
  | .ok proofData =>
    simp only [hparse] at h
    match hexec : execStepsFuel (pbcDepth proofData.steps.toList + 1)
        (BoolCheckState.fromConstrs constrs (max numVars proofData.numVars)
          objective offset)
        proofData.steps.toList with
    | some s =>
      simp only [hexec] at h
      obtain ⟨hinv, hF, hO⟩ := execStepsFuel_inv_preserve_fields _ _ s _
        (StateInv_init constrs _ objective offset) hexec
      have hF' : s.origConstrs = constrs := hF
      have hO' : s.objective = objective := hO
      match hlast : lastConclusion proofData.steps with
      | some step =>
        simp only [hlast] at h
        rw [← hF', ← hO'] at h ⊢
        exact conclusionClaim_sound s hinv offset step claim h
      | none => simp [hlast] at h
    | none => simp [hexec] at h

/-- Soundness of the Boolean entry point used by `veripb_reflect` for SAT
and BOUNDS conclusions. -/
theorem checkProofClaim_sound (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (offset : Int) (names : List (String × Nat))
    (proofStr : String) (claim : Claim)
    (h : checkProofClaimBool constrs numVars objective offset names proofStr
      claim = true) :
    claim.holds constrs objective offset :=
  proofClaim?_sound constrs numVars objective offset names proofStr claim
    (of_decide_eq_true h)

/-! ## Decidable instance for native_decide -/

instance (constrs : Array Constr) (numVars : Nat) (objective : Objective)
    (names : List (String × Nat)) (proofStr : String) :
    Decidable (checkProofBool constrs numVars objective names proofStr = true) :=
  inferInstance

/-! ## Elaboration command using reflection -/

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

/-- Build Expr for array of constraints. -/
def mkConstrArrayExpr (constrs : Array Constr) : MetaM Expr := do
  let constrType := mkConst ``Constr
  let mut elems : Array Expr := #[]
  for c in constrs do
    let termsExpr ← mkTermsExpr c.terms
    let degreeExpr := mkRawNatLit c.degree
    let constrExpr := mkApp2 (mkConst ``Constr.mk) termsExpr degreeExpr
    elems := elems.push constrExpr
  mkArrayLit constrType elems.toList
where
  mkTermsExpr (terms : List (Nat × Sat.PB.Literal)) : MetaM Expr := do
    let termType := mkApp2 (mkConst ``Prod [.zero, .zero])
      (mkConst ``Nat) (mkConst ``Sat.PB.Literal)
    let mut elems : List Expr := []
    for (coeff, lit) in terms do
      let coeffExpr := mkRawNatLit coeff
      let litExpr := match lit with
        | .pos i => mkApp (mkConst ``Sat.PB.Literal.pos) (mkRawNatLit i)
        | .neg i => mkApp (mkConst ``Sat.PB.Literal.neg) (mkRawNatLit i)
      let termExpr := mkApp4 (mkConst ``Prod.mk [.zero, .zero])
        (mkConst ``Nat) (mkConst ``Sat.PB.Literal) coeffExpr litExpr
      elems := termExpr :: elems
    mkListLit termType elems.reverse

/-- Build Expr for an objective (a term list). -/
def mkObjectiveExpr (obj : Objective) : MetaM Expr :=
  mkConstrArrayExpr.mkTermsExpr obj

/-- Expr of the empty objective `[]` (decision instances). -/
def emptyObjectiveExpr : Expr :=
  mkApp (mkConst ``List.nil [.zero])
    (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat)
      (mkConst ``Sat.PB.Literal))

/-- Expr of the empty name table `[] : List (String × Nat)` (formulas whose
variables are all written `x<N>`). -/
def emptyNamesExpr : Expr :=
  mkApp (mkConst ``List.nil [.zero])
    (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``String) (mkConst ``Nat))

/-- Build Expr for a name table `List (String × Nat)`. -/
def mkNamesExpr (names : List (String × Nat)) : MetaM Expr := do
  let pairTy := mkApp2 (mkConst ``Prod [.zero, .zero])
    (mkConst ``String) (mkConst ``Nat)
  mkListLit pairTy (names.map fun (s, i) =>
    mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``String)
      (mkConst ``Nat) (mkStrLit s) (mkRawNatLit i))

/-- `mkFormulaUnsatProof`, returning `none` if the checker rejects the
proof. -/
def mkFormulaUnsatProof? (tacName : Name) (constrsExpr numVarsExpr : Expr)
    (proofStr : String) (ref? : Option Syntax) (objExpr : Expr)
    (names : List (String × Nat)) : MetaM (Option Expr) := do
  let constrsExpr ← instantiateMVars constrsExpr
  let numVarsExpr ← instantiateMVars numVarsExpr
  let objExpr ← instantiateMVars objExpr
  let namesExpr ← if names.isEmpty then pure emptyNamesExpr
    else mkNamesExpr names
  let proofStrExpr := mkStrLit proofStr
  let checkBoolExpr := mkApp5 (mkConst ``checkProofBool)
    constrsExpr numVarsExpr objExpr namesExpr proofStrExpr
  match ← Lean.Meta.nativeEqTrue tacName checkBoolExpr (axiomDeclRange? := ref?) with
  | .success hEqTrue =>
    return some <| mkApp6 (mkConst ``checkProof_sound)
      constrsExpr numVarsExpr objExpr namesExpr proofStrExpr hEqTrue
  | .notTrue => return none

/-- Build a proof of `formulaUnsat constrs` from a VeriPB kernel proof.

`constrsExpr : Array Constr`, `numVarsExpr : Nat` and `objExpr : Objective`
must be closed terms (no free variables or metavariables); `objExpr`
defaults to the empty objective. `names` are the formula's variables not
written `x<N>` with their indices (`VeriPB.OPBInstance.names`, default
`[]`). The proof text is checked by native
evaluation of `checkProofBool` through `Lean.Meta.nativeEqTrue`, which
records a per-use axiom
`checkProofBool constrs numVars obj names proofStr = true`
(the same mechanism as `native_decide`); the result is
`checkProof_sound constrs numVars obj names proofStr ax : formulaUnsat constrs`.
An UNSAT conclusion is accepted only if the proof logs no solution.

Downstream tools that produce their own `formulaUnsat` theorems (for
example from an encoding function) should call this instead of building the
bridge term by hand. `tacName` labels the axiom; `ref?` sets its declaration
range for `#print axioms`-style tooling. -/
def mkFormulaUnsatProof (tacName : Name) (constrsExpr numVarsExpr : Expr)
    (proofStr : String) (ref? : Option Syntax := none)
    (objExpr : Expr := emptyObjectiveExpr)
    (names : List (String × Nat) := []) : MetaM Expr := do
  match ← mkFormulaUnsatProof? tacName constrsExpr numVarsExpr proofStr ref?
      objExpr names with
  | some proof => return proof
  | none => throwError "VeriPB reflection checker rejected the proof"

/-- `Expr` of a claim. -/
private def mkClaimExpr : Claim → Expr
  | .unsat => mkConst ``Claim.unsat
  | .sat => mkConst ``Claim.sat
  | .bounds lb ub => mkApp2 (mkConst ``Claim.bounds) (toExpr lb) (toExpr ub)

/-- Statement of a claim: `Claim.holds` unfolded one step. -/
private def claimTypeExpr (constrsExpr objExpr offsetExpr : Expr) : Claim → Expr
  | .unsat => mkApp (mkConst ``formulaUnsat) constrsExpr
  | .sat => mkApp (mkConst ``formulaSatisfiable) constrsExpr
  | .bounds lb ub => mkAppN (mkConst ``formulaBounds)
      #[constrsExpr, objExpr, offsetExpr, toExpr lb, toExpr ub]

/-- Build a proof of `claim.holds constrs obj offset` from a VeriPB kernel
proof, by native evaluation of `checkProofClaimBool` (per-use axiom, as in
`mkFormulaUnsatProof`). The arguments must be closed terms. -/
def mkClaimProof (tacName : Name) (constrsExpr numVarsExpr objExpr offsetExpr : Expr)
    (proofStr : String) (claim : Claim) (ref? : Option Syntax := none)
    (names : List (String × Nat) := []) : MetaM Expr := do
  let constrsExpr ← instantiateMVars constrsExpr
  let numVarsExpr ← instantiateMVars numVarsExpr
  let objExpr ← instantiateMVars objExpr
  let offsetExpr ← instantiateMVars offsetExpr
  let namesExpr ← if names.isEmpty then pure emptyNamesExpr
    else mkNamesExpr names
  let args := #[constrsExpr, numVarsExpr, objExpr, offsetExpr, namesExpr,
    mkStrLit proofStr, mkClaimExpr claim]
  let checkBoolExpr := mkAppN (mkConst ``checkProofClaimBool) args
  match ← Lean.Meta.nativeEqTrue tacName checkBoolExpr (axiomDeclRange? := ref?) with
  | .success hEqTrue => return mkAppN (mkConst ``checkProofClaim_sound) (args.push hEqTrue)
  | .notTrue => throwError "VeriPB reflection checker rejected the proof"

/-- The last `conclusion` line of a proof text is `conclusion UNSAT`. -/
private def lastConclusionIsUnsat (proofStr : String) : Bool :=
  let ls := (proofStr.splitOn "\n").filterMap fun l =>
    let t := l.trimAscii.toString
    if t.startsWith "conclusion" then some t else none
  match ls.getLast? with
  | some t => ((t.drop "conclusion".length).trimAscii.toString).startsWith "UNSAT"
  | none => false

/-- Human-readable form of a bound. -/
private def showBound : Option Int → String
  | none => "INF"
  | some v => toString v

/-- `veripb_reflect name "file.opb" "proof.pbp"` checks a VeriPB kernel proof
by reflection and registers a theorem matching the proof's conclusion (which
must close the proof: `output NONE ; conclusion ... ; end pseudo-Boolean
proof ;`):
* `conclusion UNSAT : id` (no logged solution): `name : formulaUnsat F`;
* `conclusion SAT [: lits]`: `name : formulaSatisfiable F`;
* `conclusion BOUNDS lb : id ub [: lits]`:
  `name : formulaBounds F obj offset lb ub` (`INF` is `none`).
The objective in the statement is the normalized min-form `objVal obj v +
offset` (normalized nonnegative terms `obj`, constant `offset`). For
`max: f` the parser negates the objective, so the statement is about `−f`:
`lb` gives `f ≤ −lb` for every solution and `ub` gives a solution with
`f ≥ −ub`. -/
elab "veripb_reflect " n:ident
    ppSpace opbFile:str ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let opbPath := opbFile.getString
  let proofPath := proofFile.getString
  liftTermElabM do
    let opbStr ← IO.FS.readFile (System.FilePath.mk opbPath)
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath)
    let inst ← match VeriPB.parseOPBNamed opbStr with
      | .ok r => pure r
      | .error e => throwError "OPB parse error: {e}"
    let (objective, offset, fromMax) : Objective × Int × Bool :=
      match inst.objective with
      | some o => (o.terms, o.offset, o.fromMax)
      | none => ([], 0, false)
    let constrsExpr ← mkConstrArrayExpr inst.constrs
    let numVarsExpr := mkRawNatLit inst.numVars
    let objExpr ← mkObjectiveExpr objective
    let offsetExpr := toExpr offset
    let register (type value : Expr) (what : String) : TermElabM Unit := do
      addAndCompile <| Declaration.thmDecl {
        name
        levelParams := []
        type := type
        value := value
      }
      Lean.logInfo m!"Registered {name} : {what} (checked via reflection)"
    let maxNote := if fromMax then
      " [max: objective, bounds on its negation]" else ""
    -- UNSAT without solution logging: the established `checkProofBool` path
    if lastConclusionIsUnsat proofStr then
      if let some proof ← mkFormulaUnsatProof? `veripb_reflect
          constrsExpr numVarsExpr proofStr (some (← getRef)) objExpr inst.names then
        register (mkApp (mkConst ``formulaUnsat) constrsExpr) proof
          "formulaUnsat"
        return
      -- rejected: `proofClaim?` below rejects it too (it can only differ if
      -- the text scan and the parser disagree on the last conclusion)
    match proofClaim? inst.constrs inst.numVars objective offset inst.names
        proofStr with
    | none => throwError "VeriPB reflection checker rejected the proof"
    | some claim =>
      let proof ← mkClaimProof `veripb_reflect constrsExpr numVarsExpr objExpr
        offsetExpr proofStr claim (ref? := some (← getRef)) (names := inst.names)
      let what := match claim with
        | .unsat => "formulaUnsat"
        | .sat => "formulaSatisfiable"
        | .bounds lb ub =>
          s!"formulaBounds, {showBound lb} ≤ objective ≤ {showBound ub}{maxNote}"
      register (claimTypeExpr constrsExpr objExpr offsetExpr claim) proof what

end VeriPB.Reflect
