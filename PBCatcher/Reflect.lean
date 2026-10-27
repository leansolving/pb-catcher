/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import Lean
import Std
import PBCatcher.PseudoBoolean
import PBCatcher.FromVeriPB
import PBCatcher.ReflectCheck
import PBCatcher.ReflectFast

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
`PBCatcher.ReflectCheck` (list-based, the definitions the proofs
reason about) and `PBCatcher.ReflectFast` (array-based runtime
replacement).  The step loop itself stays here, next to its soundness
proofs.  This module ties the two checkers together with
`@[implemented_by]`, proves soundness, and provides the `veripb_reflect`
command.

## Trust assumptions

Using `native_decide` adds the Lean compiler to the trusted code base.
This is the same trust model as Lean's built-in `bv_decide` tactic.

## Main definitions

* `PBCatcher.Reflect.checkProofBool` — Boolean checker for VeriPB proofs
* `PBCatcher.Reflect.StateInv` — optimization-preserving invariant (every
  solution of the formula below the threshold `best` has a database
  counterpart that is at least as good under the current objective, and the
  witnessed value `bestWit` is attained by a solution; under
  `strengthening_to_core` the core implies the database, `CoreImplied`, which
  justifies core-only `red` goals; every order stored by `def_order` is good,
  `StoredGood`, and while an order is loaded every core model has a database
  model below it in the order, `OrdInv`), preserved by every step
  (`execStepsFuel_inv_preserve`); redundance steps are checked by
  `checkRedundance` (subproof items by `processRedItems`; with a loaded order
  `checkRedOrder`, items by `processScopedItems`), and subproofs use
  the implication lemma `execStepsFuel_implied` (their `lstep`s keep every
  valuation of the database)
* `PBCatcher.Reflect.checkProof_sound` — Soundness theorem (UNSAT)
* `PBCatcher.Reflect.execStepsFuel_bounds` — optimality after a contradiction
  when the threshold and the witnessed value coincide
* `PBCatcher.Reflect.Fast.checkProofBoolFast` — Array-based runtime replacement
  via `@[implemented_by]`
* `PBCatcher.Reflect.mkFormulaUnsatProof` — Reflection bridge term for
  external `formulaUnsat` proofs (downstream entry point)
* `veripb_reflect` — Command using reflection
-/

namespace PBCatcher.Reflect

open Sat.PB

/-! ### Step execution (total, fuel-bounded) -/

/-- Process the items of a subproof without scopes (`red` and checked `delc`
without a loaded order, the `red` items of a `spec` block (via
`checkSpecChain` and `checkRedundance`, also while an order is loaded),
`obju`, the order proofs of `def_order`; CakePB
`check_scopes`/`check_subproofs`): a top-level step (an `lstep`) runs
on the current subproof database and its result stays visible to later
items; a `proofgoal gid ... qed : h` block runs on the current database plus
the negated goal constraint `goalOf gid` and must derive the contradictory
constraint `h`, after which its constraints are dropped (only the id counter
advances). A `proofgoal` without a closing id and `scope` blocks are
rejected. Returns the final subproof state and the proved goals with their
constraints. `execFn` is the step executor (`execStepsFuel` at the next
fuel level). -/
def processRedItems
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (goalOf : String → Option Constr) :
    BoolCheckState → List PBCatcher.ProofStep → List (String × Constr) →
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
goal over `goalDb` are covered; a database goal may also be discharged by
equality with a constraint of `lookupDb`, and a numbered `proofgoal` id is
resolved in `lookupDb` as well (CakePB's `gfml`: all of the database for
`red`, the core for checked deletion). Returns the next free id
after the subproof. -/
def checkRedundance
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (st0 : BoolCheckState) (goalDb lookupDb : Std.HashMap Nat Constr)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (qedHint : Option Nat) : Option Nat :=
  let nC := rupNegate C
  let st1 := { st0 with
    db := st0.db.insert st0.nextId nC
    nextId := st0.nextId + 1 }
  match processRedItems execFn (redGoalOf subst C st0.curObj lookupDb) st1
      items [] with
  | none => none
  | some (fin, proved) =>
    let ok := match qedHint with
      | some cid => match fin.db[cid]? with
        | some c => c.isContra
        | none => false
      | none =>
        hashGoalsCovered subst C nC st0.curObj proved &&
        goalDb.toList.all fun (_, D) => dbGoalCovered subst nC lookupDb proved D
    if ok then some fin.nextId else none

/-- The items of one block of a `dom` subproof without scopes (CakePB
`check_subproofs`): the top level of the subproof or the body of a `scope`.
`cur` is the block's provenance (`none` at the top level, the scope kind in a
scope). A top-level step (an `lstep`) runs on the current database; a
`proofgoal gid ... qed : h` runs on the current database plus its premises
and must derive the contradictory constraint `h`, after which its
constraints are dropped (only the id counter advances). The premises are
`strictPrem` when `strictId gid` (the strict goal of `dom`), recorded in
`contras` with the provenance, and otherwise the negated goal constraint
`goalOf gid`, recorded in `proved` with the provenance. Everything else
(`scope` blocks included) is rejected. -/
def processGoalItems
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (goalOf : String → Option Constr) (strictId : String → Bool)
    (strictPrem : List Constr) (cur : Option PBCatcher.ScopeKind) :
    BoolCheckState → List PBCatcher.ProofStep →
      List (String × Constr × Option PBCatcher.ScopeKind) → List (Option PBCatcher.ScopeKind) →
      Option (BoolCheckState × List (String × Constr × Option PBCatcher.ScopeKind) ×
        List (Option PBCatcher.ScopeKind))
  | st, [], proved, contras => some (st, proved, contras)
  | st, item :: rest, proved, contras =>
    match item with
    | .proofgoal gid steps (some h) =>
      if steps.any innerStepForbidden then none else
      if strictId gid then
        match execFn { st with
            db := insertAll st.db st.nextId strictPrem
            nextId := st.nextId + strictPrem.length } steps.toList with
        | none => none
        | some fin =>
          match fin.db[h]? with
          | some c =>
            if c.isContra then
              processGoalItems execFn goalOf strictId strictPrem cur
                { st with nextId := fin.nextId } rest proved (cur :: contras)
            else none
          | none => none
      else
      match goalOf gid with
      | none => none
      | some G =>
        match execFn { st with
            db := st.db.insert st.nextId (negTriv G)
            nextId := st.nextId + 1 } steps.toList with
        | none => none
        | some fin =>
          match fin.db[h]? with
          | some c =>
            if c.isContra then
              processGoalItems execFn goalOf strictId strictPrem cur
                { st with nextId := fin.nextId } rest ((gid, G, cur) :: proved) contras
            else none
          | none => none
    | _ =>
      if isLStep item then
        match execFn st [item] with
        | some st' => processGoalItems execFn goalOf strictId strictPrem cur st' rest
            proved contras
        | none => none
      else none

/-- The items of a `dom` subproof with scopes (CakePB `check_scopes`): a
`scope leq|geq ... end` block runs (`processGoalItems` with the scope's
provenance) on the current database plus the scope premises `scopePrem kind`
(at fresh ids; `none` rejects the scope), and at its end the database
reverts to the pre-scope one while the id counter stays advanced, so
constraints derived inside the scope are gone. Scopes are never nested.
Every other item is processed as by `processGoalItems` at the top level
(provenance `none`). -/
def processScopedItems
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (goalOf : String → Option Constr) (strictId : String → Bool)
    (strictPrem : List Constr) (scopePrem : PBCatcher.ScopeKind → Option (List Constr)) :
    BoolCheckState → List PBCatcher.ProofStep →
      List (String × Constr × Option PBCatcher.ScopeKind) → List (Option PBCatcher.ScopeKind) →
      Option (BoolCheckState × List (String × Constr × Option PBCatcher.ScopeKind) ×
        List (Option PBCatcher.ScopeKind))
  | st, [], proved, contras => some (st, proved, contras)
  | st, item :: rest, proved, contras =>
    match item with
    | .scope kind items =>
      match scopePrem kind with
      | none => none
      | some prem =>
        match processGoalItems execFn goalOf strictId strictPrem (some kind)
            { st with
              db := insertAll st.db st.nextId prem
              nextId := st.nextId + prem.length } items.toList proved contras with
        | none => none
        | some (fin, proved', contras') =>
          processScopedItems execFn goalOf strictId strictPrem scopePrem
            { st with nextId := fin.nextId } rest proved' contras'
    | _ =>
      match processGoalItems execFn goalOf strictId strictPrem none st [item]
          proved contras with
      | none => none
      | some (st', proved', contras') =>
        processScopedItems execFn goalOf strictId strictPrem scopePrem st' rest
          proved' contras'

/-- Redundance check of `C` with witness `subst` under the loaded order
`(O, z)` (CakePB `check_red` with an order, design §5): the aux variables of
the order must be fresh for `freshDb` (the whole database before the step,
for checked deletion without the deleted id), `C`, the current objective
and the image of `ω` (`domFresh`) when the subproof has a `scope` block or
`ω` touches `z`, unless the step closes with `qed : cid` (CakePB). Then `¬C`
(normalized, `rupNegate`) is added at `st0.nextId`, the subproof items run
(`processScopedItems`; `scope leq` adds `Spec[σ≤]`, `scope geq` is
rejected), and either `qed : cid` names a contradictory constraint of the
top-level subproof database (every goal is discharged), or `#1` (`C|ω`),
the order goals `#2..#k+1` (unless `ω` does not touch `z`), the objective
goal `#k+2` and every database goal over `goalDb` are covered by goals
proved outside any scope or in `scope leq` (database goals as in
`checkRedundance`, with the lookups in `lookupDb`). Without a `scope` block
no scope premises are passed (`processScopedItems` never asks for them), so
every proved goal holds without them. Returns the next free id after the
subproof. -/
def checkRedOrder
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (st0 : BoolCheckState) (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal)
    (goalDb lookupDb freshDb : Std.HashMap Nat Constr)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (qedHint : Option Nat) : Option Nat :=
  if qedHint.isNone && (hasScope items || !untouchedOrder z subst) &&
      !domFresh O.aux freshDb (PBCatcher.normalizeConstr C) st0.curObj subst then none
  else
  let nC := rupNegate C
  let st1 := { st0 with
    db := st0.db.insert st0.nextId nC
    nextId := st0.nextId + 1 }
  let sp : PBCatcher.ScopeKind → Option (List Constr) :=
    if hasScope items then redScopePrem O z subst else fun _ => none
  match processScopedItems execFn
      (redOrdGoalOf O z subst C st0.curObj (fun n => lookupDb[n]?)) (fun _ => false) []
      sp st1 items [] [] with
  | none => none
  | some (fin, proved, _) =>
    let ok := match qedHint with
      | some cid => match fin.db[cid]? with
        | some c => c.isContra
        | none => false
      | none =>
        domHashCovered nC proved "#1" (substGoal subst C) &&
          (untouchedOrder z subst ||
            domOrderGoalsCovered nC proved 2
              (O.defs.map (substGoal (Sat.PB.Dominance.sigmaLeq O z subst)))) &&
          domObjCovered subst nC st0.curObj proved ("#" ++ toString (O.defs.length + 2)) &&
          goalDb.toList.all fun (_, D) => dbGoalCovered subst nC lookupDb (leqProved proved) D
    if ok then some fin.nextId else none

/-- The redundance check of `red` and checked `delc`: `checkRedundance`
without a loaded order, `checkRedOrder` with one. -/
def checkRedAny
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (st0 : BoolCheckState) (ord : Option (Sat.PB.Dominance.OrderData × List Sat.PB.Literal))
    (goalDb lookupDb freshDb : Std.HashMap Nat Constr)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (qedHint : Option Nat) : Option Nat :=
  match ord with
  | none => checkRedundance execFn st0 goalDb lookupDb subst C items qedHint
  | some (O, z) =>
    checkRedOrder execFn st0 O z goalDb lookupDb freshDb subst C items qedHint

/-- Redundance-based strengthening `red C : ω` with subproof `items`: the
redundance check with database goals over the whole database (core and
derived), or over the core only while `strengthening_to_core` is on (CakePB
`mk_core_fml (b ∨ tcb)`; sound because every derived constraint is then
implied by the core, the invariant clause `CoreImplied`); the "goal already
in the database" lookup always sees the whole database. While an order is
loaded the check also covers the order goals and allows `scope leq`
(`checkRedOrder`, via `checkRedAny`). Then `C` (normalized) is added after
the subproof's ids, to the core iff `strengthening_to_core` is on. -/
def redStep
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (state : BoolCheckState) (constr : PBCatcher.OPBConstr)
    (substPairs : List (String × String)) (items : List PBCatcher.ProofStep)
    (qedHint : Option Nat) : Option BoolCheckState :=
  match PBCatcher.opbConstrToPB constr with
  | .error _ => none
  | .ok C =>
    match PBCatcher.parseSubstPairs substPairs state.numVars with
    | .error _ => none
    | .ok subst =>
      let goalDb := if state.s2c then
        state.db.filter fun id _ => state.coreIds.contains id else state.db
      match checkRedAny execFn state state.ord goalDb state.db state.db subst C items
          qedHint with
      | none => none
      | some fid =>
        some { state with
          db := state.db.insert fid (PBCatcher.normalizeConstr C)
          nextId := fid + 1
          coreIds := if state.s2c then state.coreIds.insert fid else state.coreIds }

/-- Checked deletion `delc id : ω : subproof ... qed [: cid]` (CakePB
`CheckedDelete`): exactly one id, which must be core, and a subproof
(VeriPB's autoproved form is not accepted); under
`strengthening_to_core` the subproof must end with `qed : cid` (CakePB
`check_tcb_idopt`; VeriPB's extra empty-witness requirement is not
imposed). The constraint is erased, then the redundance check runs
with `C := D` against the remaining core constraints only (the subproof sees
only them; with a loaded order also the order goals, `checkRedAny`, and the
aux freshness over the whole remaining database). Without an order and
without `strengthening_to_core` the check is for parity with VeriPB/CakePB:
erasing a constraint preserves `DBOpt` on its own; with an order it keeps
`CoreValid` (design T5). Under
`strengthening_to_core` the closing `qed : cid` makes the check an
implication proof (the surviving core implies `D`), which keeps the
invariant clause `CoreImplied` (`checkRedAny_qed_implied`). -/
def delcCheckedStep
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (state : BoolCheckState) (ids : List Nat)
    (substPairs : List (String × String))
    (sub : Option (Array PBCatcher.ProofStep × Option Nat)) :
    Option BoolCheckState :=
  match ids, sub with
  | [did], some (items, qedHint) =>
    match PBCatcher.parseSubstPairs substPairs state.numVars with
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
          match checkRedAny execFn
              { state with db := coreDb, coreIds := core', coreOnly := true } state.ord
              coreDb coreDb rest subst D items.toList qedHint with
          | none => none
          | some fid =>
            some { state with db := rest, coreIds := core', nextId := fid }
  | _, _ => none

/-- `obju new|diff f : subproof items qed ;` (CakePB `check_change_obj`,
semantics.md §2.3): needs an objective and no closing `qed : id`; the
goals `#1` (`f_new ≥ f_old`) and `#2` (`f_old ≥ f_new`) are discharged
over the CORE constraints by `proofgoal` blocks, or trivially; the ids the
subproof consumed stay consumed, the database is unchanged, and the
current objective becomes `f_new` (`new`) or `f_old + f` (`diff`). Together
the two goals make the objectives equal on every core model (`objuStep_sound`),
which keeps `CoreValid` while an order is loaded; without an order only `#2`
is needed. -/
def objuStep
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (state : BoolCheckState) (kind : PBCatcher.ObjUpdateKind)
    (pobj : PBCatcher.ProofObjective) (items : List PBCatcher.ProofStep)
    (qedHint : Option Nat) : Option BoolCheckState :=
  if !state.hasObj || qedHint.isSome then none else
  match proofObjToPB pobj with
  | .error _ => none
  | .ok po =>
    let nw := objuNew kind state.curObj state.curOffset po.1 po.2
    let G1 := PBCatcher.normalizeConstr
      (objGeqConstr nw.1 nw.2 state.curObj state.curOffset)
    let G2 := PBCatcher.normalizeConstr
      (objGeqConstr state.curObj state.curOffset nw.1 nw.2)
    let coreDb := state.db.filter fun id _ => state.coreIds.contains id
    match processRedItems execFn (objuGoalOf G1 G2)
        { state with db := coreDb, coreOnly := true } items [] with
    | none => none
    | some (fin, proved) =>
      if objuGoalCovered "#1" G1 proved && objuGoalCovered "#2" G2 proved then
        some { state with curObj := nw.1, curOffset := nw.2, nextId := fin.nextId }
      else none

/-- Dominance check of `C` with witness `subst` under the loaded order
`(O, z)` (CakePB `Dom`, design §5): `¬C` (normalized, `rupNegate`) is added
at `st0.nextId`, the subproof items run (`processScopedItems`), and then
either the closing hint `qed : cid` names a contradictory constraint of the
top-level subproof database (every goal is discharged), or the order goals
`#1..#k` (`Def[σ≤]`), the strict goal `#k+1` (premises `Def[σ≥]`, proved by
an explicit `proofgoal` outside any scope or in `scope geq`), the objective
goal `#k+2` and the goal of every CORE constraint are covered; the "already
in the database" lookup and numbered `proofgoal` ids see the whole database.
There is no `C|ω` goal. Returns the next free id after the subproof. -/
def checkDominance
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (st0 : BoolCheckState) (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (qedHint : Option Nat) : Option Nat :=
  let nC := rupNegate C
  let st1 := { st0 with
    db := st0.db.insert st0.nextId nC
    nextId := st0.nextId + 1 }
  let k := O.defs.length
  let goalDb := st0.db.filter fun id _ => st0.coreIds.contains id
  match processScopedItems execFn (domGoalOf O z subst st0.curObj (fun n => st0.db[n]?))
      (domStrictId k) (O.defs.map (substGoal (Sat.PB.Dominance.sigmaGeq O z subst)))
      (domScopePrem O z subst) st1 items [] [] with
  | none => none
  | some (fin, proved, contras) =>
    let ok := match qedHint with
      | some cid => match fin.db[cid]? with
        | some c => c.isContra
        | none => false
      | none =>
        domOrderGoalsCovered nC proved 1
            (O.defs.map (substGoal (Sat.PB.Dominance.sigmaLeq O z subst))) &&
          contras.any provGeqOk &&
          domObjCovered subst nC st0.curObj proved ("#" ++ toString (k + 2)) &&
          goalDb.toList.all fun (_, D) =>
            dbGoalCoveredDom subst nC goalDb st0.db proved D
    if ok then some fin.nextId else none

/-- Dominance-based strengthening `dom C : ω` with subproof `items` (CakePB
`Dom`): needs a loaded order; the aux variables of the order are fresh for
the database, `C`, the current objective and the image of `ω` (`domFresh`,
checked also when the step closes with `qed : id`); then the dominance check
(`checkDominance`), and `C` (normalized) is added after the subproof's ids,
to the core iff `strengthening_to_core` is on. -/
def domStep
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (state : BoolCheckState) (constr : PBCatcher.OPBConstr)
    (substPairs : List (String × String)) (items : List PBCatcher.ProofStep)
    (qedHint : Option Nat) : Option BoolCheckState :=
  match state.ord with
  | none => none
  | some (O, z) =>
    match PBCatcher.opbConstrToPB constr with
    | .error _ => none
    | .ok C =>
      match PBCatcher.parseSubstPairs substPairs state.numVars with
      | .error _ => none
      | .ok subst =>
        if !domFresh O.aux state.db (PBCatcher.normalizeConstr C) state.curObj subst then
          none
        else
        match checkDominance execFn state O z subst C items qedHint with
        | none => none
        | some fid =>
          some { state with
            db := state.db.insert fid (PBCatcher.normalizeConstr C)
            nextId := fid + 1
            coreIds := if state.s2c then state.coreIds.insert fid else state.coreIds }

/-- The spec block of a `def_order` (CakePB `check_spec`): every item is a
`red` step whose witness maps only aux variables (`aux`), checked like a
top-level `red` (database goals over the whole database) against the spec
constraints before it, on a local database that starts empty with ids from
1 and has no objective. Returns the spec constraints (normalized) with their
witnesses, in order. -/
def checkSpecChain
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (aux : List Nat) :
    BoolCheckState → List PBCatcher.ProofStep →
      Option (List (Constr × List (Nat × Sat.PB.SubstVal)))
  | _, [] => some []
  | st, item :: rest =>
    match specRedOf item with
    | none => none
    | some (constr, pairs, items, qedHint) =>
      match PBCatcher.opbConstrToPB constr with
      | .error _ => none
      | .ok C =>
        match PBCatcher.parseSubstPairs pairs st.numVars with
        | .error _ => none
        | .ok subst =>
          if !(subst.all fun p => decide (p.1 ∈ aux)) then none
          else match checkRedundance execFn st st.db st.db subst C items qedHint with
            | none => none
            | some fid =>
              match checkSpecChain execFn aux
                  { st with db := st.db.insert fid (PBCatcher.normalizeConstr C)
                            nextId := fid + 1 } rest with
              | none => none
              | some steps => some ((PBCatcher.normalizeConstr C, subst) :: steps)

/-- An order proof block (transitivity, reflexivity; CakePB
`check_transitivity`/`check_reflexivity`): the premises at ids
`start, start+1, ...` of a local database (nothing else is visible), the
items (`lstep`s and `proofgoal #j` blocks), and every goal `#j` covered
(`hashGoalsAllCovered`). Returns the next free id after the block. -/
def checkOrderProof
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (state : BoolCheckState) (start : Nat) (prem goals : List Constr)
    (items : List PBCatcher.ProofStep) : Option Nat :=
  match processRedItems execFn (hashGoalOf goals)
      (state.withLocalDb (mkDBRec prem start) (start + prem.length)) items [] with
  | none => none
  | some (fin, proved) =>
    if hashGoalsAllCovered proved 1 goals then some fin.nextId else none

/-- `def_order` (CakePB `StoreOrder`): the spec block (`checkSpecChain`), the
well-formedness of the encoding (`orderWellFormed`), the fresh lists of the
transitivity proof (`transFresh`), the transitivity proof on its premises
from id 1, and the reflexivity proof on `Spec[v:=u]` only, with ids
continuing after the transitivity proof's. Both proofs are required. The
order is stored under its name (newest first); nothing else changes, no
global id is allocated, and a loaded order is not affected. -/
def defOrderStep
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (state : BoolCheckState) (od : PBCatcher.OrderDef PBCatcher.ProofStep) :
    Option BoolCheckState :=
  match od.transitivity, od.reflexivity with
  | some t, some refl =>
    match od.defConstrs.mapM PBCatcher.opbConstrToPB with
    | .error _ => none
    | .ok defs0 =>
      match checkSpecChain execFn od.aux (state.withLocalDb {} 1)
          (od.spec.getD #[]).toList with
      | none => none
      | some steps =>
        let O : Sat.PB.Dominance.OrderData :=
          { left := od.left, right := od.right, aux := od.aux,
            spec := steps.map Prod.fst, defs := defs0.map PBCatcher.normalizeConstr }
        if !orderWellFormed O ||
            !transFresh O t.freshRight t.freshAux1 t.freshAux2 then none
        else
          match checkOrderProof execFn state 1
              (transPremises O t.freshRight t.freshAux1 t.freshAux2)
              (transGoals O t.freshRight t.freshAux2) t.proof.toList with
          | none => none
          | some tid =>
            match checkOrderProof execFn state tid (reflPremises O) (reflGoals O)
                refl.toList with
            | none => none
            | some _ => some { state with orders := (od.name, O) :: state.orders }
  | _, _ => none

/-- `load_order NAME lits` (CakePB `LoadOrder`): the last definition of the
name, literals accepted by `loadOrderOk`; every constraint moves to the core
and the order is loaded by value. -/
def loadOrderStep (state : BoolCheckState) (name : String)
    (lits : List PBCatcher.OPBLit) : Option BoolCheckState :=
  match findOrder name state.orders with
  | none => none
  | some O =>
    match lits.mapM PBCatcher.opbLitToPB with
    | .error _ => none
    | .ok z =>
      if loadOrderOk O z then
        some { state with coreIds := allIds state.db, ord := some (O, z) }
      else none

/-- Execute proof steps with fuel for subproof nesting depth.
    Returns the final state if all steps succeed.
    Fuel is consumed only by subproofs (`pbc`, `red`, `dom`, checked `delc`,
    `def_order`, `obju`). -/
def execStepsFuel (fuel : Nat) (state : BoolCheckState)
    (steps : List PBCatcher.ProofStep) : Option BoolCheckState :=
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
            (PBCatcher.normalizeConstr result)
          some { state with db := newDb, nextId := state.nextId + 1 }
        | none => none
      | .rup constr hints =>
        match PBCatcher.opbConstrToPB constr with
        | .ok pbConstr =>
          if !verifyRupBool (rupNegate pbConstr) hints state.db
              state.numVars then none
          else
            let newDb := state.db.insert state.nextId
              (PBCatcher.normalizeConstr pbConstr)
            some { state with db := newDb, nextId := state.nextId + 1 }
        | .error _ => none
      | .ia constr premise =>
        match premise with
        | none => none
        | some pid =>
          match state.db[pid]? with
          | none => none
          | some S =>
            match PBCatcher.opbConstrToPB constr with
            | .error _ => none
            | .ok T0 =>
              if impliesSyntactic (PBCatcher.normalizeConstr S)
                  (PBCatcher.normalizeConstr T0) then
                some { state with
                  db := state.db.insert state.nextId (PBCatcher.normalizeConstr T0)
                  nextId := state.nextId + 1 }
              else none
      | .pbc constr innerSteps resultId =>
        if innerSteps.any innerStepForbidden then none
        else match fuel with
        | 0 => none
        | n + 1 =>
          match PBCatcher.opbConstrToPB constr with
          | .ok pbConstr =>
            if pbConstr.degree > pbConstr.coeffSum then none
            else
              let savedDb := state.db
              let negId := state.nextId
              let dbWithNeg := state.db.insert negId
                (PBCatcher.normalizeConstr pbConstr.negate)
              let subState : BoolCheckState :=
                { state with db := dbWithNeg, nextId := negId + 1 }
              match execStepsFuel n subState innerSteps.toList with
              | some finalSub =>
                match finalSub.db[resultId]? with
                | some c =>
                  if !c.isContra then none
                  else
                    let restoredDb := savedDb.insert finalSub.nextId
                      (PBCatcher.normalizeConstr pbConstr)
                    some { state with
                      db := restoredDb
                      nextId := finalSub.nextId + 1 }
                | none => none
              | none => none
          | .error _ => none
      -- `red` and checked `delc` get the order goals while an order is
      -- loaded (`checkRedAny`); `obju` runs unchanged, its two objective
      -- goals give the equality the invariant needs
      | .red constr substPairs goals =>
        match fuel with
        | 0 => none
        | n + 1 =>
          redStep (execStepsFuel n) state constr substPairs (goalsToItems goals) none
      -- dominance: needs a loaded order (`domStep`)
      | .dom constr substPairs goals =>
        match fuel with
        | 0 => none
        | n + 1 =>
          domStep (execStepsFuel n) state constr substPairs (goalsToItems goals) none
      | .strengthening rule constr substPairs items qedHint =>
        match rule with
        | .dom =>
          match fuel with
          | 0 => none
          | n + 1 =>
            domStep (execStepsFuel n) state constr substPairs items.toList qedHint
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
        -- `deld` deletes derived constraints only (VeriPB, CakePB); inside
        -- a core-only subproof every constraint is core
        if ids.any state.coreIds.contains ||
            (state.coreOnly && ids.any state.db.contains) then none
        else some { state with
          db := ids.foldl (fun db id => db.erase id) state.db
          coreIds := ids.foldl (fun s id => s.erase id) state.coreIds }
      | .delc ids =>
        -- unchecked deletion; while an order is loaded or under
        -- `strengthening_to_core` CakePB requires every constraint to be core;
        -- checked deletion is off from here on
        if (state.ord.isSome || state.s2c) && !allCore state then none
        else some { state with
          db := ids.foldl (fun db id => db.erase id) state.db
          coreIds := ids.foldl (fun s id => s.erase id) state.coreIds
          chk := false }
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
      | .loadOrder (some name) lits => loadOrderStep state name lits
      -- unloading needs a loaded order (CakePB `UnloadOrder`)
      | .loadOrder none _ =>
        if state.ord.isSome then some { state with ord := none } else none
      | .defOrder od =>
        match fuel with
        | 0 => none
        | n + 1 => defOrderStep (execStepsFuel n) state od
      | .output => some state
      | .conclusionNone => some state
      | .conclusion id =>
        match state.db[id]? with
        | some c => if c.isContra then some state else none
        | none => none
      -- solution logging: the solution satisfies the original formula; its
      -- value under the current objective is checked against `: v`, lowers
      -- the threshold `best` and (`soli`) gives the improvement constraint;
      -- its value under the original objective lowers `bestWit` while
      -- checked deletion is on (CakePB `bound`, VeriPB
      -- `best_valid_objective_value`)
      | .sol lits value =>
        match checkSolutionVals state.origConstrs state.objective
            state.curObj lits with
        | none => none
        | some (bo, bc) =>
          if !solValueOk state.curOffset bc value then none
          else some { state with
            best := updBest state.best ((bc : Int) + state.curOffset)
            bestWit := updBestWit state.chk state.bestWit
              ((bo : Int) + state.offset) }
      | .soli lits value =>
        match checkSolutionVals state.origConstrs state.objective
            state.curObj lits with
        | none => none
        | some (bo, bc) =>
          if !solValueOk state.curOffset bc value then none
          else some { state with
            db := state.db.insert state.nextId (improveConstr state.curObj bc)
            nextId := state.nextId + 1
            best := updBest state.best ((bc : Int) + state.curOffset)
            bestWit := updBestWit state.chk state.bestWit
              ((bo : Int) + state.offset)
            coreIds := state.coreIds.insert state.nextId }
      -- `obji v`: no solution; the improvement constraint for the value `v`
      -- (core) and the threshold are updated, `bestWit` is not
      | .obji v =>
        if !state.hasObj then none
        else some { state with
          db := state.db.insert state.nextId
            (objiConstr state.curObj state.curOffset v)
          nextId := state.nextId + 1
          best := updBest state.best v
          coreIds := state.coreIds.insert state.nextId }
      -- objective statements (P2b): `eobj` checks, `obju` changes the
      -- current objective after a core-only subproof
      | .eobj pobj =>
        if eobjOk state.hasObj state.curObj state.curOffset pobj then some state
        else none
      | .obju kind pobj (some (items, qedHint)) =>
        match fuel with
        | 0 => none
        | n + 1 => objuStep (execStepsFuel n) state kind pobj items.toList qedHint
      | .obju _ _ none => none  -- CakePB: the subproof is required
      -- output claims: checked as the footer (`outputClaimOk`)
      | .outputClaim _ _ => some state
      | .conclusionSat _ => some state
      | .conclusionBounds _ _ _ _ => some state
      | _ => none  -- statements the checker does not support yet
    match stepResult with
    | some s => execStepsFuel fuel s rest
    | none => none
termination_by (fuel, steps.length)

/-- Main Boolean checker: returns true iff the proof is a valid UNSAT proof
of `constrs` (logging no value: no `sol`, `soli` or `obji`) with respect to
`objective` (`[]` for decision instances; the objective only matters for
solution logging, `obji` and the red objective goal; the offset is fixed at
0 on this path, which cannot change the verdict). `names` lists the formula's variables that are not
written `x<N>`, with their indices (`PBCatcher.OPBInstance.names`, `[]` when
all are `x<N>`); the proof parser needs them to resolve such names. The
checker's variable count is `numVars` raised to the parser's count, which
includes the fresh (extension) variables the proof introduces. -/
@[implemented_by Fast.checkProofBoolFast]
def checkProofBool (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (names : List (String × Nat))
    (proofStr : String) : Bool :=
  match PBCatcher.parseVeriPBProofWith (PBCatcher.VarTable.ofList names numVars)
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
(with the objective's constant `offset`, the initial `curOffset`, against
which `sol`/`soli` values, `obji` and the bounds are read) and returns the
claim its conclusion certifies on the final state (`conclusionClaim`), with
the footer placed and its output step accepted (`lastFooter`,
`outputClaimOk`), or `none` if a step, the footer or the conclusion is
rejected. `checkProofClaim_sound` gives the meaning (`Claim.holds`). -/
@[implemented_by Fast.proofClaimFast?]
def proofClaim? (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (offset : Int) (names : List (String × Nat))
    (proofStr : String) : Option Claim :=
  match PBCatcher.parseVeriPBProofWith (PBCatcher.VarTable.ofList names numVars)
      proofStr with
  | .error _ => none
  | .ok proofData =>
    let initState := BoolCheckState.fromConstrs constrs
      (max numVars proofData.numVars) objective offset
    let fuel := pbcDepth proofData.steps.toList + 1
    match execStepsFuel fuel initState proofData.steps.toList with
    | some s =>
      match lastFooter proofData.steps with
      | some (o, step) =>
        if outputClaimOk s.conclCtx o then
          conclusionClaim (fun id => s.db[id]?) constrs s.conclCtx step
        else none
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
    (h : PBCatcher.findZeroIdx terms = some idx) : idx < terms.length := by
  simp only [PBCatcher.findZeroIdx] at h
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
    (h : PBCatcher.findZeroIdx terms = some idx) : terms[idx].1 = 0 := by
  simp only [PBCatcher.findZeroIdx] at h
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
    (PBCatcher.normalizeConstr.go fuel terms degree).sat v := by
  induction fuel generalizing terms degree with
  | zero => simp only [PBCatcher.normalizeConstr.go]; exact h
  | succ n ih =>
    simp only [PBCatcher.normalizeConstr.go]
    cases hzero : PBCatcher.findZeroIdx terms with
    | some idx =>
      apply ih; have hidx := findZeroIdx_lt terms idx hzero
      have hcoeff := findZeroIdx_zero terms idx hidx hzero
      rw [evalSum_remove_zero v terms idx hidx hcoeff]; exact h
    | none =>
      cases hpair : PBCatcher.findValidCompPairIdx terms degree with
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
        cases hlike : PBCatcher.findLikeTermIdx terms with
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
    (PBCatcher.normalizeConstr c).sat v := by
  simp only [PBCatcher.normalizeConstr, Constr.sat] at *
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
    (v : Valuation) (h : (PBCatcher.normalizeConstr.go fuel terms degree).sat v) :
    Sat.PB.evalSum v terms ≥ degree := by
  induction fuel generalizing terms degree with
  | zero => simp only [PBCatcher.normalizeConstr.go] at h; exact h
  | succ n ih =>
    simp only [PBCatcher.normalizeConstr.go] at h
    cases hzero : PBCatcher.findZeroIdx terms with
    | some idx =>
      rw [hzero] at h
      have hidx := findZeroIdx_lt terms idx hzero
      have hcoeff := findZeroIdx_zero terms idx hidx hzero
      have hih := ih _ _ h
      rw [← evalSum_remove_zero v terms idx hidx hcoeff]; exact hih
    | none =>
      rw [hzero] at h
      cases hpair : PBCatcher.findValidCompPairIdx terms degree with
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
        cases hlike : PBCatcher.findLikeTermIdx terms with
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
    (h : (PBCatcher.normalizeConstr c).sat v) : c.sat v := by
  simp only [PBCatcher.normalizeConstr, Constr.sat] at *
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
  have h2 := constrMatchNorm_sat (PBCatcher.normalizeConstr c)
    (PBCatcher.normalizeConstr dbC) v hmatch h1
  exact normalize_sat_rev c v h2

-- execPolOps soundness: each pol operation preserves implication

/-- All constraints on a stack are implied by the original formula. -/
def StackSound (original : Array Constr) (_db : Std.HashMap Nat Constr)
    (stack : List PBCatcher.StackElem) : Prop :=
  ∀ se ∈ stack, match se with
    | .constr c => ∀ v : Valuation,
        (∀ c' ∈ original.toList, Constr.sat c' v) → Constr.sat c v
    | .nat _ => True

-- StackSound helpers
private theorem StackSound_cons_constr (original : Array Constr)
    (db : Std.HashMap Nat Constr) (c : Constr)
    (stack : List PBCatcher.StackElem)
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
    (stack : List PBCatcher.StackElem)
    (hstack : StackSound original db stack) :
    StackSound original db (.nat n :: stack) := by
  intro se hse
  cases hse with
  | head => exact True.intro
  | tail _ h => exact hstack se h

private theorem StackSound_tail (original : Array Constr)
    (db : Std.HashMap Nat Constr) (x : PBCatcher.StackElem)
    (stack : List PBCatcher.StackElem)
    (h : StackSound original db (x :: stack)) :
    StackSound original db stack :=
  fun se hse => h se (.tail _ hse)

private theorem StackSound_head_constr (original : Array Constr)
    (db : Std.HashMap Nat Constr) (c : Constr)
    (stack : List PBCatcher.StackElem)
    (h : StackSound original db (.constr c :: stack)) :
    ∀ v : Valuation,
      (∀ c' ∈ original.toList, Constr.sat c' v) → Constr.sat c v :=
  h (.constr c) (.head _)

/-- Weakening by a variable preserves satisfaction: the removed terms
contribute at most their coefficient sum, which is subtracted from the
degree (truncated). -/
private theorem weakenConstr_sat (c : Constr) (varIdx : Nat) (v : Valuation)
    (hsat : c.sat v) : (PBCatcher.weakenConstr c varIdx).sat v := by
  simp only [PBCatcher.weakenConstr, Constr.sat] at *
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
    (k : Nat) (c : Constr) (rest stack' : List PBCatcher.StackElem)
    (hstack : StackSound original db (.nat k :: .constr c :: rest))
    (hexec : (if k == 0 then none
      else some (PBCatcher.StackElem.constr (f (PBCatcher.normalizeConstr c) k) :: rest))
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
    (original : Array Constr) (stack stack' : List PBCatcher.StackElem)
    (op : PBCatcher.PolOp)
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
    match hlit : PBCatcher.opbLitToPB lit with
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
    (original : Array Constr) (ops : List PBCatcher.PolOp)
    (stack stack' : List PBCatcher.StackElem)
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

theorem execPolRPNBool_implied (ops : List PBCatcher.PolOp)
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
    (h : PBCatcher.RupHint) (rc : Constr)
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
    ∀ {hints : List PBCatcher.RupHint} {cs : List Constr},
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
  by_cases hle : (PBCatcher.normalizeConstr c).degree ≤ (PBCatcher.normalizeConstr c).coeffSum
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
    (hints : List PBCatcher.RupHint) (db : Std.HashMap Nat Constr)
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
theorem lsteps_of_not_any (steps : Array PBCatcher.ProofStep)
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
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (goalOf : String → Option Constr)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v) :
    ∀ (items : List PBCatcher.ProofStep) (st : BoolCheckState)
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
that satisfies `C` and the goal database `goalDb` and has an objective value
no larger than that of `w`. `goalDb` and `lookupDb` are satisfied by every
model of the database (the whole database or a part of it). -/
theorem checkRedundance_sound
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (st0 : BoolCheckState) (goalDb lookupDb : Std.HashMap Nat Constr)
    (hgoal : ∀ v, DBSatBy st0.db v → DBSatBy goalDb v)
    (hlook : ∀ v, DBSatBy st0.db v → DBSatBy lookupDb v)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (qedHint : Option Nat) (fid : Nat)
    (h : checkRedundance execFn st0 goalDb lookupDb subst C items qedHint =
      some fid)
    (w : Valuation) (hw : DBSatBy st0.db w) (hC : ¬ C.sat w) :
    C.sat (Sat.PB.applyValuation subst w) ∧
      DBSatBy goalDb (Sat.PB.applyValuation subst w) ∧
      objVal st0.curObj (Sat.PB.applyValuation subst w) ≤
        objVal st0.curObj w := by
  have hnC : (rupNegate C).sat w := rupNegate_sat_of_not_sat C w hC
  have hw1 : DBSatBy (st0.db.insert st0.nextId (rupNegate C)) w :=
    DBSatBy_insert _ _ _ w hw hnC
  unfold checkRedundance at h
  dsimp only at h
  cases hp : processRedItems execFn (redGoalOf subst C st0.curObj lookupDb) { st0 with db := st0.db.insert st0.nextId (rupNegate C), nextId := st0.nextId + 1 } items [] with
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
      by_cases hok : (hashGoalsCovered subst C (rupNegate C) st0.curObj proved &&
          goalDb.toList.all fun x => dbGoalCovered subst (rupNegate C) lookupDb proved x.snd) = true
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
          have hmem : (id, D) ∈ goalDb.toList := by
            rw [Std.HashMap.get?_eq_getElem?] at hget
            exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget
          have hcov := List.all_eq_true.mp hall (id, D) hmem
          exact dbGoalCovered_sound subst _ lookupDb proved D w hcov
            (hlook w hw) (hgoal w hw id D hget) hnC hproved
        · rcases h2 with hna | (htr | hpr) | himp
          · show Sat.PB.evalSum _ st0.curObj ≤ _
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

/-- A redundance check closed by `qed : cid` is an implication proof: the
subproof derives a contradiction from the database plus `¬C`, so every
model of the database satisfies `C` (checked deletion under
`strengthening_to_core`). -/
theorem checkRedundance_qed_implied
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (st0 : BoolCheckState) (goalDb lookupDb : Std.HashMap Nat Constr)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (cid fid : Nat)
    (h : checkRedundance execFn st0 goalDb lookupDb subst C items (some cid) =
      some fid) :
    ∀ w, DBSatBy st0.db w → C.sat w := by
  intro w hw
  apply Classical.byContradiction
  intro hC
  have hw1 : DBSatBy (st0.db.insert st0.nextId (rupNegate C)) w :=
    DBSatBy_insert _ _ _ w hw (rupNegate_sat_of_not_sat C w hC)
  unfold checkRedundance at h
  dsimp only at h
  cases hp : processRedItems execFn (redGoalOf subst C st0.curObj lookupDb) { st0 with db := st0.db.insert st0.nextId (rupNegate C), nextId := st0.nextId + 1 } items [] with
  | none => rw [hp] at h; cases h
  | some r =>
    obtain ⟨fin, proved⟩ := r
    rw [hp] at h
    dsimp only at h
    have hfin := (processRedItems_sound execFn _ hexec items _ [] fin proved
      hp w hw1 (by simp)).1
    cases hc : fin.db[cid]? with
    | none => simp [hc] at h
    | some c =>
      by_cases hcon : c.isContra = true
      · exact contra_unsat c w (by simpa [Constr.isContra] using hcon)
          (hfin cid c (by rwa [Std.HashMap.get?_eq_getElem?]))
      · simp [hc, hcon] at h

/-! ### Id counter monotonicity -/

/-- The items of a redundance subproof never decrease the id counter (for
an `execFn` that never decreases it on `lstep`s). -/
theorem processRedItems_nextId_le
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (goalOf : String → Option Constr)
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId) :
    ∀ (items : List PBCatcher.ProofStep) (st : BoolCheckState)
      (proved : List (String × Constr)) (fin : BoolCheckState)
      (proved' : List (String × Constr)),
      processRedItems execFn goalOf st items proved = some (fin, proved') →
      st.nextId ≤ fin.nextId := by
  intro items
  induction items with
  | nil =>
    intro st proved fin proved' h
    simp only [processRedItems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Nat.le_refl _
  | cons item rest ih =>
    intro st proved fin proved' h
    simp only [processRedItems] at h
    split at h
    · rename_i gid steps hid
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
          have h1 := hmono _ fin' steps.toList hls hx
          cases hc : fin'.db[hid]? with
          | none => rw [hc] at h; cases h
          | some c =>
            rw [hc] at h
            simp only [] at h
            by_cases hcon : c.isContra = true
            · rw [if_pos hcon] at h
              have h2 := ih _ _ fin proved' h
              simp only [] at h1 h2
              omega
            · rw [if_neg hcon] at h; cases h
    · split at h
      · rename_i hl
        cases hx : execFn st [item] with
        | none => rw [hx] at h; cases h
        | some st' =>
          rw [hx] at h
          simp only [] at h
          exact Nat.le_trans (hmono st st' [item] (by simpa using hl) hx)
            (ih st' proved fin proved' h)
      · cases h

/-- The redundance check returns an id at or above the counter it started
from. -/
theorem checkRedundance_nextId_le
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId)
    (st0 : BoolCheckState) (goalDb lookupDb : Std.HashMap Nat Constr)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (qedHint : Option Nat) (fid : Nat)
    (h : checkRedundance execFn st0 goalDb lookupDb subst C items qedHint =
      some fid) :
    st0.nextId ≤ fid := by
  unfold checkRedundance at h
  dsimp only at h
  cases hp : processRedItems execFn (redGoalOf subst C st0.curObj lookupDb) { st0 with db := st0.db.insert st0.nextId (rupNegate C), nextId := st0.nextId + 1 } items [] with
  | none => rw [hp] at h; cases h
  | some r =>
    obtain ⟨fin, proved⟩ := r
    rw [hp] at h
    dsimp only at h
    have h1 := processRedItems_nextId_le execFn _ hmono items _ [] fin proved hp
    simp only [] at h1
    have key : ∀ b : Bool, (if b = true then some fin.nextId else none) =
        some fid → st0.nextId ≤ fid := by
      intro b hb
      cases b
      · simp at hb
      · simp only [ite_true, Option.some.injEq] at hb; omega
    exact key _ h

/-- The formula, the original objective and the two best values are
unchanged (what a step must keep besides the database relation). -/
structure KeepsObj (st state : BoolCheckState) : Prop where
  origConstrs : st.origConstrs = state.origConstrs
  objective : st.objective = state.objective
  offset : st.offset = state.offset
  best : st.best = state.best
  bestWit : st.bestWit = state.bestWit

/-- `KeepsObj`, and the current objective is unchanged as well. -/
structure SameObjFields (st state : BoolCheckState) : Prop
    extends KeepsObj st state where
  curObj : st.curObj = state.curObj
  curOffset : st.curOffset = state.curOffset

theorem objGeqConstr_sound (f : Objective) (c : Int) (g : Objective) (d : Int)
    (w : Valuation) (h : (objGeqConstr f c g d).sat w) :
    opbVal g d w ≤ opbVal f c w := by
  have hle := Sat.PB.evalSum_le_coeffSumR w g
  have hneg : Sat.PB.evalSum w (g.map fun (a, l) => (a, l.negate)) +
      Sat.PB.evalSum w g = Sat.PB.coeffSumR g := Sat.PB.evalSum_negate_eq w g
  have happ : Sat.PB.evalSum w (f ++ g.map fun (a, l) => (a, l.negate)) =
      Sat.PB.evalSum w f + Sat.PB.evalSum w (g.map fun (a, l) => (a, l.negate)) :=
    Sat.PB.evalSum_append w _ _
  have h' : ((Sat.PB.coeffSumR g : Int) + d - c).toNat ≤
      Sat.PB.evalSum w (f ++ g.map fun (a, l) => (a, l.negate)) := h
  simp only [opbVal, objVal]
  generalize Sat.PB.evalSum w (g.map fun (a, l) => (a, l.negate)) = n at hneg happ
  generalize Sat.PB.evalSum w (f ++ g.map fun (a, l) => (a, l.negate)) = m
    at happ h'
  omega

theorem DBSatBy_filter (db : Std.HashMap Nat Constr) (p : Nat → Constr → Bool)
    (w : Valuation) (h : DBSatBy db w) : DBSatBy (db.filter p) w := by
  intro id c hget
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter',
    Option.filter_eq_some_iff] at hget
  exact h id c (by rw [Std.HashMap.get?_eq_getElem?]; exact hget.1)

/-! ### Core constraints and the id counter -/

/-- `ρ` satisfies every core constraint of `db` (the ids in `core`). -/
def CoreSatBy (db : Std.HashMap Nat Constr) (core : Std.HashSet Nat)
    (ρ : Valuation) : Prop :=
  ∀ id c, core.contains id = true → db.get? id = some c → c.sat ρ

/-- Every id of `db` lies below `n` (the id counter), so inserting at `n` or
above never overwrites a constraint. -/
def IdsBelowDb (db : Std.HashMap Nat Constr) (n : Nat) : Prop :=
  ∀ id c, db.get? id = some c → id < n

theorem DBSatBy_filter_core_iff (db : Std.HashMap Nat Constr)
    (core : Std.HashSet Nat) (ρ : Valuation) :
    DBSatBy (db.filter fun id _ => core.contains id) ρ ↔ CoreSatBy db core ρ := by
  constructor
  · intro h id c hid hget
    apply h id c
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter',
      Option.filter_eq_some_iff]
    exact ⟨by rwa [← Std.HashMap.get?_eq_getElem?], hid⟩
  · intro h id c hget
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter',
      Option.filter_eq_some_iff] at hget
    exact h id c hget.2 (by rw [Std.HashMap.get?_eq_getElem?]; exact hget.1)

theorem CoreSatBy_of_DBSatBy {db : Std.HashMap Nat Constr}
    {core : Std.HashSet Nat} {ρ : Valuation} (h : DBSatBy db ρ) :
    CoreSatBy db core ρ :=
  fun id c _ hget => h id c hget

/-- A smaller core is satisfied as well. -/
theorem CoreSatBy_mono {db : Std.HashMap Nat Constr}
    {core core' : Std.HashSet Nat} {ρ : Valuation}
    (hsub : ∀ id, core.contains id = true → core'.contains id = true)
    (h : CoreSatBy db core' ρ) : CoreSatBy db core ρ :=
  fun id c hid hget => h id c (hsub id hid) hget

/-- Inserting at a fresh id does not change the old core constraints. -/
theorem CoreSatBy_of_insert_fresh {db : Std.HashMap Nat Constr}
    {core core' : Std.HashSet Nat} {ρ : Valuation} {k : Nat} {c : Constr}
    (hk : db.get? k = none)
    (hsub : ∀ id, core.contains id = true → core'.contains id = true)
    (h : CoreSatBy (db.insert k c) core' ρ) : CoreSatBy db core ρ := by
  intro id c' hid hget
  apply h id c' (hsub id hid)
  rw [HashMap_get?_insert]
  have hne : (k == id) = false := by
    cases heq : k == id
    · rfl
    · rw [beq_iff_eq] at heq; subst heq; rw [hk] at hget; cases hget
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  exact hget

/-- `CoreImplied` survives the insertion of an implied constraint at a fresh
id into the derived set. -/
theorem coreImplied_insert_implied {db : Std.HashMap Nat Constr}
    {core : Std.HashSet Nat} {k : Nat} {c : Constr}
    (hk : db.get? k = none) (himpl : ∀ ρ, DBSatBy db ρ → c.sat ρ)
    (h : ∀ ρ, CoreSatBy db core ρ → DBSatBy db ρ) :
    ∀ ρ, CoreSatBy (db.insert k c) core ρ → DBSatBy (db.insert k c) ρ := by
  intro ρ hρ
  have hdb := h ρ (CoreSatBy_of_insert_fresh hk (fun _ hid => hid) hρ)
  exact DBSatBy_insert _ _ _ ρ hdb (himpl ρ hdb)

/-- `CoreImplied` survives the insertion of any constraint at a fresh id into
the core. -/
theorem coreImplied_insert_core {db : Std.HashMap Nat Constr}
    {core : Std.HashSet Nat} {k : Nat} {c : Constr}
    (hk : db.get? k = none)
    (h : ∀ ρ, CoreSatBy db core ρ → DBSatBy db ρ) :
    ∀ ρ, CoreSatBy (db.insert k c) (core.insert k) ρ →
      DBSatBy (db.insert k c) ρ := by
  intro ρ hρ
  have hsub : ∀ id, core.contains id = true → (core.insert k).contains id = true :=
    fun id hid => by rw [Std.HashSet.contains_insert, hid, Bool.or_true]
  have hdb := h ρ (CoreSatBy_of_insert_fresh hk hsub hρ)
  refine DBSatBy_insert _ _ _ ρ hdb (hρ k c ?_ ?_)
  · rw [Std.HashSet.contains_insert]; simp
  · rw [HashMap_get?_insert]; simp

theorem IdsBelowDb_fresh {db : Std.HashMap Nat Constr} {n k : Nat}
    (h : IdsBelowDb db n) (hk : n ≤ k) : db.get? k = none := by
  cases hg : db.get? k with
  | none => rfl
  | some c => have := h k c hg; omega

theorem IdsBelowDb_mono {db : Std.HashMap Nat Constr} {n n' : Nat}
    (h : IdsBelowDb db n) (hn : n ≤ n') : IdsBelowDb db n' :=
  fun id c hg => Nat.lt_of_lt_of_le (h id c hg) hn

theorem IdsBelowDb_insert {db : Std.HashMap Nat Constr} {n n' k : Nat}
    {c : Constr} (h : IdsBelowDb db n) (hk : k < n') (hn : n ≤ n') :
    IdsBelowDb (db.insert k c) n' := by
  intro id c' hg
  rw [HashMap_get?_insert] at hg
  by_cases heq : k == id
  · rw [beq_iff_eq] at heq; subst heq; exact hk
  · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hg
    exact Nat.lt_of_lt_of_le (h id c' hg) hn

theorem HashMap_get?_erase_fold (db : Std.HashMap Nat Constr) (ids : List Nat)
    (k : Nat) :
    (ids.foldl (fun db id => db.erase id) db).get? k =
      if k ∈ ids then none else db.get? k := by
  induction ids generalizing db with
  | nil => simp
  | cons id rest ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_erase]
    by_cases h1 : k = id
    · subst h1; simp
    · by_cases h2 : k ∈ rest
      · simp [h2]
      · have : (id == k) = false := by
          cases hb : id == k
          · rfl
          · rw [beq_iff_eq] at hb; exact absurd hb.symm h1
        simp [h1, h2, this]

theorem HashSet_contains_erase_fold (s : Std.HashSet Nat) (ids : List Nat)
    (k : Nat) (h : s.contains k = true) (hk : k ∉ ids) :
    (ids.foldl (fun s id => s.erase id) s).contains k = true := by
  induction ids generalizing s with
  | nil => simpa using h
  | cons id rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · rw [Std.HashSet.contains_erase, h]
      have hne : (id == k) = false := by
        cases hb : id == k
        · rfl
        · rw [beq_iff_eq] at hb; subst hb; simp at hk
      simp [hne]
    · exact fun hm => hk (List.mem_cons_of_mem _ hm)

theorem IdsBelowDb_erase_fold {db : Std.HashMap Nat Constr} {n : Nat}
    (ids : List Nat) (h : IdsBelowDb db n) :
    IdsBelowDb (ids.foldl (fun db id => db.erase id) db) n := by
  intro id c hg
  rw [HashMap_get?_erase_fold] at hg
  by_cases hm : id ∈ ids
  · simp [hm] at hg
  · simp only [hm, ↓reduceIte] at hg; exact h id c hg

theorem HashSet_contains_insert_fold (s : Std.HashSet Nat) (ids : List Nat)
    (k : Nat) (h : s.contains k = true ∨ k ∈ ids) :
    (ids.foldl (fun s id => s.insert id) s).contains k = true := by
  induction ids generalizing s with
  | nil => simpa using h
  | cons id rest ih =>
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · left; rw [Std.HashSet.contains_insert, h, Bool.or_true]
    · rcases List.mem_cons.mp h with h | h
      · left; subst h; rw [Std.HashSet.contains_insert]; simp
      · right; exact h

theorem HashSet_contains_insert_fold_if (s : Std.HashSet Nat) (ids : List Nat)
    (p : Nat → Prop) [DecidablePred p] (k : Nat) (h : s.contains k = true) :
    (ids.foldl (fun s id => if p id then s.insert id else s) s).contains k =
      true := by
  induction ids generalizing s with
  | nil => simpa using h
  | cons id rest ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · rw [Std.HashSet.contains_insert, h, Bool.or_true]
    · exact h

theorem HashMap_get?_some_mem_keys {db : Std.HashMap Nat Constr} {id : Nat}
    {c : Constr} (h : db.get? id = some c) : id ∈ db.keys := by
  rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_isSome_getElem?,
    ← Std.HashMap.get?_eq_getElem?, h]
  rfl

theorem allIds_contains {db : Std.HashMap Nat Constr} {id : Nat} {c : Constr}
    (h : db.get? id = some c) : (allIds db).contains id = true :=
  HashSet_contains_insert_fold _ _ _ (Or.inr (HashMap_get?_some_mem_keys h))

theorem allCore_contains {s : BoolCheckState} (h : allCore s = true) {id : Nat}
    {c : Constr} (hg : s.db.get? id = some c) : s.coreIds.contains id = true :=
  List.all_eq_true.mp h id (HashMap_get?_some_mem_keys hg)

theorem objuGoalCovered_sat (gid : String) (G : Constr)
    (proved : List (String × Constr)) (w : Valuation)
    (h : objuGoalCovered gid G proved = true) (hpr : ∀ p ∈ proved, p.2.sat w) :
    G.sat w := by
  simp only [objuGoalCovered, Bool.or_eq_true] at h
  rcases h with (hdeg | htriv) | hany
  · simp only [Constr.sat]
    rw [beq_iff_eq.mp hdeg]
    exact Nat.zero_le _
  · exact trivialByPair_sat G w htriv
  · obtain ⟨p, hpm, hpc⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true] at hpc
    exact constrMatchNorm_sat _ _ w hpc.2 (hpr p hpm)

/-- `obju` keeps the formula, the original objective and the best values,
leaves the database unchanged, and every core model has the same value under
the new and the old objective (goals `#1` and `#2`, proved over the core; a
single inequality would not keep `CoreValid` while an order is loaded). -/
theorem objuStep_sound
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (state : BoolCheckState) (kind : PBCatcher.ObjUpdateKind)
    (pobj : PBCatcher.ProofObjective) (items : List PBCatcher.ProofStep)
    (qedHint : Option Nat) (st' : BoolCheckState)
    (h : objuStep execFn state kind pobj items qedHint = some st') :
    KeepsObj st' state ∧ st'.db = state.db ∧
      ∀ w, CoreSatBy state.db state.coreIds w →
        opbVal st'.curObj st'.curOffset w =
          opbVal state.curObj state.curOffset w := by
  unfold objuStep at h
  split at h
  · cases h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h
      · rename_i fin proved hp
        split at h
        · rename_i hcov
          cases h
          refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, fun w hw => ?_⟩
          have hcore : DBSatBy (state.db.filter fun id _ =>
              state.coreIds.contains id) w := (DBSatBy_filter_core_iff _ _ _).mpr hw
          have hpr := (processRedItems_sound execFn _ hexec items _ [] fin
            proved hp w hcore (by simp)).2
          simp only [Bool.and_eq_true] at hcov
          exact Int.le_antisymm
            (objGeqConstr_sound _ _ _ _ w (normalize_sat_rev _ w
              (objuGoalCovered_sat _ _ proved w hcov.2 hpr)))
            (objGeqConstr_sound _ _ _ _ w (normalize_sat_rev _ w
              (objuGoalCovered_sat _ _ proved w hcov.1 hpr)))
        · cases h

/-- `obju` leaves the database, the core and the mode unchanged and never
decreases the id counter. -/
theorem objuStep_shape
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId)
    (state : BoolCheckState) (kind : PBCatcher.ObjUpdateKind)
    (pobj : PBCatcher.ProofObjective) (items : List PBCatcher.ProofStep)
    (qedHint : Option Nat) (st' : BoolCheckState)
    (h : objuStep execFn state kind pobj items qedHint = some st') :
    st'.db = state.db ∧ st'.coreIds = state.coreIds ∧ st'.s2c = state.s2c ∧
      state.nextId ≤ st'.nextId ∧ st'.ord = state.ord ∧ st'.orders = state.orders := by
  unfold objuStep at h
  split at h
  · cases h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h
      · rename_i fin proved hp
        split at h
        · cases h
          have h1 := processRedItems_nextId_le execFn _ hmono items _ [] fin
            proved hp
          exact ⟨rfl, rfl, rfl, h1, rfl, rfl⟩
        · cases h

/-! ### Orders: soundness of `def_order` -/

theorem DBSatBy_empty (ρ : Valuation) : DBSatBy ({} : Std.HashMap Nat Constr) ρ :=
  fun id c h => by rw [HashMap_get?_empty] at h; cases h

/-- Inserting at a fresh id adds exactly one constraint. -/
theorem DBSatBy_insert_fresh_iff {db : Std.HashMap Nat Constr} {k : Nat}
    {c : Constr} {ρ : Valuation} (hk : db.get? k = none) :
    DBSatBy (db.insert k c) ρ ↔ DBSatBy db ρ ∧ c.sat ρ := by
  constructor
  · intro h
    refine ⟨fun id c' hget => h id c' ?_, h k c (by rw [HashMap_get?_insert]; simp)⟩
    rw [HashMap_get?_insert]
    have hne : (k == id) = false := by
      cases heq : k == id
      · rfl
      · rw [beq_iff_eq] at heq; subst heq; rw [hk] at hget; cases hget
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact hget
  · exact fun ⟨h1, h2⟩ => DBSatBy_insert _ _ _ _ h1 h2

/-- The database `mkDBRec cs i` is satisfied by every model of `cs`. -/
theorem DBSatBy_mkDBRec {cs : List Constr} {i : Nat} {ρ : Valuation}
    (h : ∀ c ∈ cs, c.sat ρ) : DBSatBy (mkDBRec cs i) ρ :=
  fun id c hget => h c (mkDBRec_mem cs i id c hget)

/-- The spec block's checks give a redundance chain (`RedChain`, the
hypothesis of `spec_valid`): each spec constraint is derivable by redundance
from the ones before it with a witness supported in the aux variables. The
local database holds exactly the earlier spec constraints (`hdb`) at ids
below its counter. -/
theorem checkSpecChain_sound
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId)
    (aux : List Nat) :
    ∀ (items : List PBCatcher.ProofStep) (st : BoolCheckState) (pre : List Constr)
      (steps : List (Constr × List (Nat × Sat.PB.SubstVal))),
      checkSpecChain execFn aux st items = some steps →
      (∀ ρ, DBSatBy st.db ρ ↔ ∀ c ∈ pre, c.sat ρ) →
      IdsBelowDb st.db st.nextId →
      Sat.PB.Dominance.RedChain aux pre steps := by
  intro items
  induction items with
  | nil =>
    intro st pre steps h _ _
    simp only [checkSpecChain, Option.some.injEq] at h
    subst h
    exact trivial
  | cons item rest ih =>
    intro st pre steps h hdb hib
    simp only [checkSpecChain] at h
    cases hsr : specRedOf item with
    | none => rw [hsr] at h; cases h
    | some r =>
      obtain ⟨constr, pairs, items, qedHint⟩ := r
      rw [hsr] at h
      dsimp only at h
      cases hc : PBCatcher.opbConstrToPB constr with
      | error _ => rw [hc] at h; cases h
      | ok C =>
        rw [hc] at h
        dsimp only at h
        cases hs : PBCatcher.parseSubstPairs pairs st.numVars with
        | error _ => rw [hs] at h; cases h
        | ok subst =>
          rw [hs] at h
          dsimp only at h
          by_cases hsupp : (subst.all fun p => decide (p.1 ∈ aux)) = true
          · rw [if_neg (by simp [hsupp])] at h
            cases hchk : checkRedundance execFn st st.db st.db subst C items qedHint with
            | none => rw [hchk] at h; cases h
            | some fid =>
              rw [hchk] at h
              dsimp only at h
              cases hrest : checkSpecChain execFn aux
                  { st with db := st.db.insert fid (PBCatcher.normalizeConstr C),
                            nextId := fid + 1 } rest with
              | none => rw [hrest] at h; cases h
              | some steps' =>
                rw [hrest] at h
                simp only [Option.some.injEq] at h
                subst h
                have hfid := checkRedundance_nextId_le execFn hmono _ _ _ _ _ _ _ fid hchk
                have hk : st.db.get? fid = none := IdsBelowDb_fresh hib hfid
                refine ⟨?_, ?_, ?_⟩
                · intro p hp
                  have := List.all_eq_true.mp hsupp p hp
                  simpa using this
                · intro ρ hpre hg
                  have hC : ¬ C.sat ρ := fun hc => hg (normalize_sat C ρ hc)
                  obtain ⟨h1, h2, -⟩ := checkRedundance_sound execFn hexec st st.db st.db
                    (fun _ hv => hv) (fun _ hv => hv) subst C items qedHint fid hchk ρ
                    ((hdb ρ).mpr hpre) hC
                  intro c hcm
                  rcases List.mem_append.mp hcm with hcm | hcm
                  · exact (hdb _).mp h2 c hcm
                  · rw [List.mem_singleton] at hcm
                    subst hcm
                    exact normalize_sat C _ h1
                · apply ih _ (pre ++ [PBCatcher.normalizeConstr C]) steps' hrest
                  · intro ρ
                    show DBSatBy (st.db.insert fid (PBCatcher.normalizeConstr C)) ρ ↔ _
                    rw [DBSatBy_insert_fresh_iff hk, hdb ρ]
                    constructor
                    · intro ⟨h1, h2⟩ c hcm
                      rcases List.mem_append.mp hcm with hcm | hcm
                      · exact h1 c hcm
                      · rw [List.mem_singleton] at hcm; subst hcm; exact h2
                    · intro h
                      exact ⟨fun c hcm => h c (List.mem_append_left _ hcm),
                        h _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))⟩
                  · exact IdsBelowDb_insert hib (Nat.lt_succ_self _)
                      (by show st.nextId ≤ fid + 1; omega)
          · rw [if_pos (by simpa using hsupp)] at h; cases h

/-- Covered order-proof goals hold for every valuation satisfying the proved
goals. -/
theorem hashGoalsAllCovered_sound (proved : List (String × Constr)) (ρ : Valuation)
    (hpr : ∀ p ∈ proved, p.2.sat ρ) :
    ∀ (j : Nat) (goals : List Constr), hashGoalsAllCovered proved j goals = true →
      ∀ G ∈ goals, G.sat ρ := by
  intro j goals
  induction goals generalizing j with
  | nil => intro _ G hG; cases hG
  | cons G gs ih =>
    intro h G' hG'
    simp only [hashGoalsAllCovered, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hG' with rfl | hG'
    · exact objuGoalCovered_sat _ _ proved ρ h.1 hpr
    · exact ih (j + 1) h.2 G' hG'

/-- An order proof block is an entailment proof: every valuation satisfying
the premises satisfies every goal (a `proofgoal #j` derives a contradiction
from the premises plus the negated goal; trivial goals hold everywhere). -/
theorem checkOrderProof_sound
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (state : BoolCheckState) (start : Nat) (prem goals : List Constr)
    (items : List PBCatcher.ProofStep) (tid : Nat)
    (h : checkOrderProof execFn state start prem goals items = some tid) :
    ∀ ρ, (∀ c ∈ prem, c.sat ρ) → ∀ G ∈ goals, G.sat ρ := by
  intro ρ hρ
  unfold checkOrderProof at h
  cases hp : processRedItems execFn (hashGoalOf goals)
      (state.withLocalDb (mkDBRec prem start) (start + prem.length)) items [] with
  | none => rw [hp] at h; cases h
  | some r =>
    obtain ⟨fin, proved⟩ := r
    rw [hp] at h
    dsimp only at h
    have hpr := (processRedItems_sound execFn _ hexec items _ [] fin proved hp ρ
      (DBSatBy_mkDBRec hρ) (by simp)).2
    by_cases hcov : hashGoalsAllCovered proved 1 goals = true
    · exact hashGoalsAllCovered_sound proved ρ hpr 1 goals hcov
    · rw [if_neg hcov] at h; cases h

/-- Normalized substituted constraints hold where the substituted ones do. -/
theorem substGoal_map_sat {σ : List (Nat × Sat.PB.SubstVal)} {cs : List Constr}
    {ρ : Valuation} (h : ∀ g ∈ cs, (Sat.PB.applySubstConstr σ g).sat ρ) :
    ∀ c ∈ cs.map (substGoal σ), c.sat ρ := by
  intro c hc
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hc
  exact normalize_sat _ ρ (h g hg)

/-- A satisfied normalized substituted goal gives the substituted constraint. -/
theorem applySubst_of_substGoal_sat {σ : List (Nat × Sat.PB.SubstVal)}
    {cs : List Constr} {ρ : Valuation} (h : ∀ c ∈ cs.map (substGoal σ), c.sat ρ) :
    ∀ g ∈ cs, (Sat.PB.applySubstConstr σ g).sat ρ :=
  fun g hg => normalize_sat_rev _ ρ (h _ (List.mem_map.mpr ⟨g, hg, rfl⟩))

/-- `def_order` stores an order whose encoding is a valid specification with a
reflexive and transitive induced relation (`GoodOrder`), and changes nothing
else. -/
theorem defOrderStep_spec
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId)
    (state : BoolCheckState) (od : PBCatcher.OrderDef PBCatcher.ProofStep)
    (st' : BoolCheckState) (h : defOrderStep execFn state od = some st') :
    ∃ O, Sat.PB.Dominance.GoodOrder O ∧
      st' = { state with orders := (od.name, O) :: state.orders } := by
  unfold defOrderStep at h
  split at h
  · rename_i t refl _ _
    split at h
    · cases h
    · rename_i defs0 _
      split at h
      · cases h
      · rename_i steps hsteps
        dsimp only at h
        split at h
        · cases h
        · rename_i hok
          split at h
          · cases h
          · rename_i tid htr
            split at h
            · cases h
            · rename_i rid hrf
              simp only [Option.some.injEq] at h
              subst h
              refine ⟨_, ?_, rfl⟩
              simp only [Bool.or_eq_true, Bool.not_eq_true', not_or,
                Bool.not_eq_false] at hok
              obtain ⟨hwfb, hfrb⟩ := hok
              simp only [orderWellFormed, Bool.and_eq_true, beq_iff_eq,
                decide_eq_true_eq, List.all_eq_true] at hwfb
              obtain ⟨⟨hlen, hnd⟩, hv⟩ := hwfb
              simp only [transFresh, Bool.and_eq_true, beq_iff_eq,
                decide_eq_true_eq] at hfrb
              obtain ⟨⟨⟨hw, hb⟩, hc⟩, hfresh⟩ := hfrb
              have hchain := checkSpecChain_sound execFn hexec hmono od.aux _ _ [] steps
                hsteps (fun ρ => ⟨fun _ c hc => absurd hc List.not_mem_nil,
                  fun _ => DBSatBy_empty ρ⟩)
                (fun id c hg => by
                  show id < 1
                  simp only [BoolCheckState.withLocalDb] at hg
                  rw [HashMap_get?_empty] at hg; cases hg)
              have hspec := Sat.PB.Dominance.spec_valid
                (O := ⟨od.left, od.right, od.aux, steps.map Prod.fst,
                  defs0.map PBCatcher.normalizeConstr⟩) rfl hchain
              have htrans := checkOrderProof_sound execFn hexec _ _ _ _ _ _ htr
              have hrefl := checkOrderProof_sound execFn hexec _ _ _ _ _ _ hrf
              refine ⟨⟨hlen, hnd⟩, hv, hspec, ?_, ?_⟩
              · refine Sat.PB.Dominance.refl_of_goals ⟨hlen, hnd⟩ hv hspec ?_
                intro ρ hs
                exact applySubst_of_substGoal_sat
                  (hrefl ρ (substGoal_map_sat hs))
              · refine Sat.PB.Dominance.trans_of_goals ⟨hlen, hnd⟩ hv hspec hw hb hc
                  hfresh ?_
                intro ρ h1 h2 h3 h4 h5
                refine applySubst_of_substGoal_sat (htrans ρ ?_)
                intro x hx
                simp only [transPremises, List.mem_append] at hx
                rcases hx with (((hx | hx) | hx) | hx) | hx
                · exact h1 x hx
                · exact substGoal_map_sat h2 x hx
                · exact substGoal_map_sat h3 x hx
                · exact h4 x hx
                · exact substGoal_map_sat h5 x hx
  · cases h

theorem findOrder_mem {name : String} {O : Sat.PB.Dominance.OrderData} :
    ∀ {l : List (String × Sat.PB.Dominance.OrderData)},
      findOrder name l = some O → (name, O) ∈ l
  | [], h => by simp [findOrder] at h
  | (n, O') :: rest, h => by
    simp only [findOrder] at h
    by_cases hn : (n == name) = true
    · rw [if_pos hn] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [beq_iff_eq] at hn; subst hn
      exact List.mem_cons_self
    · rw [if_neg hn] at h
      exact List.mem_cons_of_mem _ (findOrder_mem h)

/-- A `load_order` loads a stored order with accepted literals, moves every
constraint to the core, and changes nothing else. -/
theorem loadOrderStep_spec (state : BoolCheckState) (name : String)
    (lits : List PBCatcher.OPBLit) (st' : BoolCheckState)
    (h : loadOrderStep state name lits = some st') :
    ∃ O z, (name, O) ∈ state.orders ∧ z.length = O.left.length ∧
      (∀ l ∈ z, l.var ∉ O.aux) ∧
      st' = { state with coreIds := allIds state.db, ord := some (O, z) } := by
  unfold loadOrderStep at h
  cases hf : findOrder name state.orders with
  | none => rw [hf] at h; cases h
  | some O =>
    rw [hf] at h
    dsimp only at h
    cases hz : lits.mapM PBCatcher.opbLitToPB with
    | error _ => rw [hz] at h; cases h
    | ok z =>
      rw [hz] at h
      dsimp only at h
      by_cases hok : loadOrderOk O z = true
      · rw [if_pos hok] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [loadOrderOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
          decide_eq_true_eq] at hok
        exact ⟨O, z, findOrder_mem hf, hok.1, hok.2, rfl⟩
      · rw [if_neg hok] at h; cases h

/-- Subproof lemma: a sequence of `lstep`s keeps every valuation of the
database (they derive implied constraints or delete). Used for `pbc`
subproofs, `proofgoal` blocks and the top level of redundance subproofs. -/
theorem execStepsFuel_implied : ∀ (fuel : Nat)
    (state state' : BoolCheckState) (steps : List PBCatcher.ProofStep),
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
        match hparse : PBCatcher.opbConstrToPB constr with
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
            cases hparse : PBCatcher.opbConstrToPB constr with
            | error _ => simp [hparse] at hsteps
            | ok T0 =>
              simp only [hparse] at hsteps
              by_cases himp : impliesSyntactic (PBCatcher.normalizeConstr S)
                  (PBCatcher.normalizeConstr T0) = true
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
            match hparse : PBCatcher.opbConstrToPB constr with
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
                        db := state.db.insert state.nextId
                          (PBCatcher.normalizeConstr pbConstr.negate)
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
                        hinner v (DBSatBy_insert _ _ _ v hv
                          (normalize_sat _ v hneg_sat))
                      exact contra_unsat c v (by
                        simp [Constr.isContra] at hcontra; exact hcontra)
                        (hfin resultId c (by rwa [Std.HashMap.get?_eq_getElem?]))
                    · simp [hcontra] at hsteps
                  | none => simp [hres] at hsteps
                | none => simp [hinner] at hsteps
            | .error _ => simp [hparse] at hsteps
      | deld ids =>
        cases hc : (ids.any state.coreIds.contains ||
            (state.coreOnly && ids.any state.db.contains)) with
        | true => simp [hc] at hsteps
        | false =>
          simp only [hc, Bool.false_eq_true, ↓reduceIte] at hsteps
          intro v hv
          exact ih_rest _ hsteps v (DBSatBy_erase_fold state.db ids v hv)
      | _ => simp [isLStep] at hl


/-- A sequence of `lstep`s never decreases the id counter (`pbc` inserts its
result at the counter its subproof ends with). -/
theorem execStepsFuel_nextId_le : ∀ (fuel : Nat)
    (state state' : BoolCheckState) (steps : List PBCatcher.ProofStep),
    (∀ s ∈ steps, isLStep s = true) →
    execStepsFuel fuel state steps = some state' →
    state.nextId ≤ state'.nextId := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih_fuel =>
    intro state state' steps hls hsteps
    induction steps generalizing state with
    | nil =>
      unfold execStepsFuel at hsteps
      injection hsteps with h; subst h; exact Nat.le_refl _
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
          have h1 := ih_rest _ hsteps
          dsimp only at h1
          omega
        | none => simp [hpol] at hsteps
      | rup constr hints =>
        match hparse : PBCatcher.opbConstrToPB constr with
        | .ok pbConstr =>
          simp [hparse] at hsteps
          by_cases hrup : verifyRupBool (rupNegate pbConstr) hints
              state.db state.numVars = false
          · simp [hrup] at hsteps
          · simp [hrup] at hsteps
            have h1 := ih_rest _ hsteps
            dsimp only at h1
            omega
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
            cases hparse : PBCatcher.opbConstrToPB constr with
            | error _ => simp [hparse] at hsteps
            | ok T0 =>
              simp only [hparse] at hsteps
              by_cases himp : impliesSyntactic (PBCatcher.normalizeConstr S)
                  (PBCatcher.normalizeConstr T0) = true
              · rw [if_pos himp] at hsteps
                have h1 := ih_rest _ hsteps
                dsimp only at h1
                omega
              · rw [if_neg himp] at hsteps; simp at hsteps
      | pbc constr innerSteps resultId =>
        by_cases hany : innerSteps.any innerStepForbidden = true
        · simp [hany] at hsteps
        · simp [hany] at hsteps
          match fuel with
          | 0 => simp at hsteps
          | n + 1 =>
            match hparse : PBCatcher.opbConstrToPB constr with
            | .ok pbConstr =>
              simp [hparse] at hsteps
              by_cases hcs : pbConstr.degree > pbConstr.coeffSum
              · simp [hcs] at hsteps
              · simp [hcs] at hsteps
                match hinner :
                    execStepsFuel n
                      { state with
                        db := state.db.insert state.nextId
                          (PBCatcher.normalizeConstr pbConstr.negate)
                        nextId := state.nextId + 1 }
                      innerSteps.toList with
                | some finalSub =>
                  simp [hinner] at hsteps
                  have h0 := ih_fuel n (by omega) _ finalSub
                    innerSteps.toList (lsteps_of_not_any innerSteps hany) hinner
                  dsimp only at h0
                  match hres : finalSub.db[resultId]? with
                  | some c =>
                    simp [hres] at hsteps
                    by_cases hcontra : c.isContra
                    · simp [hcontra] at hsteps
                      have h1 := ih_rest _ hsteps
                      dsimp only at h1
                      omega
                    · simp [hcontra] at hsteps
                  | none => simp [hres] at hsteps
                | none => simp [hinner] at hsteps
            | .error _ => simp [hparse] at hsteps
      | deld ids =>
        cases hc : (ids.any state.coreIds.contains ||
            (state.coreOnly && ids.any state.db.contains)) with
        | true => simp [hc] at hsteps
        | false =>
          simp only [hc, Bool.false_eq_true, ↓reduceIte] at hsteps
          have h1 := ih_rest _ hsteps
          exact h1
      | _ => simp [isLStep] at hl

/-! ## Optimization-preserving invariant

The top-level invariant follows CakePB's semantics for optimization (its
`dbound`/`bound` split): every solution of the original formula `F` whose
original objective value lies below the threshold `best` (lowered by `sol`,
`soli` and `obji`) has a counterpart satisfying the database whose value
under the current objective is at least as good, and the witnessed value
`bestWit` (lowered by `sol`/`soli` only) is the original objective value of
an actual solution of `F`. For a decision instance (no logged value) this
says: if `F` is satisfiable, so is the database. -/

/-- `v` satisfies every constraint of the formula. -/
def FormulaSat (F : Array Constr) (v : Valuation) : Prop :=
  ∀ c ∈ F.toList, c.sat v

/-- `v` lies below the threshold `best` under the original objective
(vacuous before any value is logged). -/
def Improving (obj : Objective) (offset : Int) (best : Option Int)
    (v : Valuation) : Prop :=
  ∀ b, best = some b → opbVal obj offset v < b

/-- Every improving solution of `F` (original objective `obj`, `offset`)
has a database counterpart that is at least as good under the current
objective `curObj`, `curOffset`. -/
def DBOpt (F : Array Constr) (obj : Objective) (offset : Int)
    (best : Option Int) (curObj : Objective) (curOffset : Int)
    (db : Std.HashMap Nat Constr) : Prop :=
  ∀ v, FormulaSat F v → Improving obj offset best v →
    ∃ w, DBSatBy db w ∧ opbVal curObj curOffset w ≤ opbVal obj offset v

/-- The best witnessed value is attained by a solution of `F` under the
original objective. -/
def BestWitnessed (F : Array Constr) (obj : Objective) (offset : Int)
    (bestWit : Option Int) : Prop :=
  ∀ b, bestWit = some b → ∃ ρ, FormulaSat F ρ ∧ opbVal obj offset ρ = b

/-- While `strengthening_to_core` is on, every model of the core satisfies
the whole database (design D3): the derived constraints are implied by the
core. This is what lets `red` database goals range over the core only. -/
def CoreImplied (s : BoolCheckState) : Prop :=
  s.s2c = true → ∀ ρ, CoreSatBy s.db s.coreIds ρ → DBSatBy s.db ρ

/-- The core constraints of a database (the ids in `core`), as a list. -/
def coreList (db : Std.HashMap Nat Constr) (core : Std.HashSet Nat) : List Constr :=
  (db.filter fun id _ => core.contains id).toList.map Prod.snd

/-- All constraints of a database, as a list. -/
def dbList (db : Std.HashMap Nat Constr) : List Constr := db.toList.map Prod.snd

theorem forall_dbList_iff (db : Std.HashMap Nat Constr) (ρ : Valuation) :
    (∀ c ∈ dbList db, c.sat ρ) ↔ DBSatBy db ρ := by
  constructor
  · intro h id c hget
    apply h
    rw [Std.HashMap.get?_eq_getElem?] at hget
    exact List.mem_map.mpr ⟨(id, c),
      Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget, rfl⟩
  · intro h c hc
    obtain ⟨⟨id, c'⟩, hmem, rfl⟩ := List.mem_map.mp hc
    exact h id _ (by
      rw [Std.HashMap.get?_eq_getElem?]
      exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem)

theorem forall_coreList_iff (db : Std.HashMap Nat Constr) (core : Std.HashSet Nat)
    (ρ : Valuation) :
    (∀ c ∈ coreList db core, c.sat ρ) ↔ CoreSatBy db core ρ :=
  (forall_dbList_iff _ ρ).trans (DBSatBy_filter_core_iff db core ρ)

/-- `Sat.PB.Dominance.CoreValid` on the core and the whole database, stated on
the hash maps: every core model has a database model below it in the loaded
order with an objective value no larger. -/
def CoreValidDB (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal)
    (db : Std.HashMap Nat Constr) (core : Std.HashSet Nat)
    (f : Valuation → Int) : Prop :=
  ∀ ρ, CoreSatBy db core ρ → ∃ ρ', DBSatBy db ρ' ∧
    Sat.PB.Dominance.Leq O z ρ' ρ ∧ f ρ' ≤ f ρ

theorem coreValid_iff_DB {O : Sat.PB.Dominance.OrderData} {z : List Sat.PB.Literal}
    {db : Std.HashMap Nat Constr} {core : Std.HashSet Nat} {f : Valuation → Int} :
    Sat.PB.Dominance.CoreValid O z (coreList db core) (dbList db) f ↔
      CoreValidDB O z db core f := by
  constructor
  · intro h ρ hρ
    obtain ⟨ρ', h1, h2, h3⟩ := h ρ ((forall_coreList_iff db core ρ).mpr hρ)
    exact ⟨ρ', (forall_dbList_iff db ρ').mp h1, h2, h3⟩
  · intro h ρ hρ
    obtain ⟨ρ', h1, h2, h3⟩ := h ρ ((forall_coreList_iff db core ρ).mp hρ)
    exact ⟨ρ', (forall_dbList_iff db ρ').mpr h1, h2, h3⟩

/-- Every stored order is good: its spec is valid and the induced relation is
reflexive and transitive (design T7, checked by `def_order`). -/
def StoredGood (s : BoolCheckState) : Prop :=
  ∀ p ∈ s.orders, Sat.PB.Dominance.GoodOrder p.2

/-- While an order is loaded: it is good, its literals fit it and avoid its
aux variables, and every core model has a database model below it in the
order that is at least as good under the current objective (`CoreValid`,
design §3; what the dominance rule needs). -/
def OrdInv (s : BoolCheckState) : Prop :=
  ∀ O z, s.ord = some (O, z) → Sat.PB.Dominance.GoodOrder O ∧
    z.length = O.left.length ∧ (∀ l ∈ z, l.var ∉ O.aux) ∧
    Sat.PB.Dominance.CoreValid O z (coreList s.db s.coreIds) (dbList s.db)
      (opbVal s.curObj s.curOffset)

/-- An implied constraint at a fresh id joins the derived set. -/
theorem coreValidDB_insert_implied {O : Sat.PB.Dominance.OrderData}
    {z : List Sat.PB.Literal} {db : Std.HashMap Nat Constr} {core : Std.HashSet Nat}
    {f : Valuation → Int} {k : Nat} {c : Constr} (hk : db.get? k = none)
    (himpl : ∀ ρ, DBSatBy db ρ → c.sat ρ) (h : CoreValidDB O z db core f) :
    CoreValidDB O z (db.insert k c) core f := by
  intro ρ hρ
  obtain ⟨ρ', h1, h2, h3⟩ := h ρ (CoreSatBy_of_insert_fresh hk (fun _ hid => hid) hρ)
  exact ⟨ρ', DBSatBy_insert _ _ _ _ h1 (himpl ρ' h1), h2, h3⟩

/-- A constraint closed downwards under `f` joins core and database at a fresh
id (`soli`, `obji`; `Sat.PB.Dominance.coreValid_cons_bound`). -/
theorem coreValidDB_insert_bound {O : Sat.PB.Dominance.OrderData}
    {z : List Sat.PB.Literal} {db : Std.HashMap Nat Constr} {core : Std.HashSet Nat}
    {f : Valuation → Int} {k : Nat} {c : Constr} (hk : db.get? k = none)
    (hdown : ∀ ρ ρ', f ρ' ≤ f ρ → c.sat ρ → c.sat ρ')
    (h : CoreValidDB O z db core f) :
    CoreValidDB O z (db.insert k c) (core.insert k) f := by
  intro ρ hρ
  have hsub : ∀ id, core.contains id = true → (core.insert k).contains id = true :=
    fun id hid => by rw [Std.HashSet.contains_insert, hid, Bool.or_true]
  obtain ⟨ρ', h1, h2, h3⟩ := h ρ (CoreSatBy_of_insert_fresh hk hsub hρ)
  have hc : c.sat ρ := hρ k c (by rw [Std.HashSet.contains_insert]; simp)
    (by rw [HashMap_get?_insert]; simp)
  exact ⟨ρ', DBSatBy_insert _ _ _ _ h1 (hdown ρ ρ' h3 hc), h2, h3⟩

/-- A core whose models are models of the old core keeps `CoreValidDB`
(`Sat.PB.Dominance.coreValid_mono_C`). -/
theorem coreValidDB_mono_core {O : Sat.PB.Dominance.OrderData}
    {z : List Sat.PB.Literal} {db : Std.HashMap Nat Constr}
    {core core' : Std.HashSet Nat} {f : Valuation → Int}
    (hsub : ∀ ρ, CoreSatBy db core' ρ → CoreSatBy db core ρ)
    (h : CoreValidDB O z db core f) : CoreValidDB O z db core' f :=
  fun ρ hρ => h ρ (hsub ρ hρ)

/-- Deleting derived constraints keeps `CoreValidDB` (`deld`;
`Sat.PB.Dominance.coreValid_mono_B`). -/
theorem coreValidDB_erase_derived {O : Sat.PB.Dominance.OrderData}
    {z : List Sat.PB.Literal} {db : Std.HashMap Nat Constr} {core : Std.HashSet Nat}
    {f : Valuation → Int} (ids : List Nat)
    (hnc : ∀ id ∈ ids, core.contains id = false) (h : CoreValidDB O z db core f) :
    CoreValidDB O z (ids.foldl (fun db id => db.erase id) db)
      (ids.foldl (fun s id => s.erase id) core) f := by
  intro ρ hρ
  obtain ⟨ρ', h1, h2, h3⟩ := h ρ (by
    intro id c hid hget
    have hnot : id ∉ ids := fun hm => by rw [hnc id hm] at hid; cases hid
    exact hρ id c (HashSet_contains_erase_fold _ _ _ hid hnot)
      (by rw [HashMap_get?_erase_fold, if_neg hnot]; exact hget))
  exact ⟨ρ', DBSatBy_erase_fold db ids ρ' h1, h2, h3⟩

/-- `load_order`: with every constraint in the core, reflexivity gives
`CoreValidDB` with the identity counterpart (`Sat.PB.Dominance.coreValid_refl`). -/
theorem coreValidDB_allIds {O : Sat.PB.Dominance.OrderData}
    {z : List Sat.PB.Literal} {db : Std.HashMap Nat Constr} {f : Valuation → Int}
    (hrefl : ∀ p, p.length = O.left.length → O.Rel p p)
    (hz : z.length = O.left.length) : CoreValidDB O z db (allIds db) f :=
  fun ρ hρ => ⟨ρ, fun id c hget => hρ id c (allIds_contains hget) hget,
    Sat.PB.Dominance.leq_refl hrefl hz ρ, Int.le_refl _⟩

/-- A constraint over the negated objective literals is closed downwards
under the objective (the `soli` and `obji` constraints). -/
theorem negObj_sat_mono (obj : Objective) (d : Nat) (ρ ρ' : Valuation)
    (hle : objVal obj ρ' ≤ objVal obj ρ)
    (h : (⟨obj.map fun x => (x.1, x.2.negate), d⟩ : Constr).sat ρ) :
    (⟨obj.map fun x => (x.1, x.2.negate), d⟩ : Constr).sat ρ' := by
  have e1 : Sat.PB.evalSum ρ (obj.map fun x => (x.1, x.2.negate)) +
      Sat.PB.evalSum ρ obj = Sat.PB.coeffSumR obj := Sat.PB.evalSum_negate_eq ρ obj
  have e2 : Sat.PB.evalSum ρ' (obj.map fun x => (x.1, x.2.negate)) +
      Sat.PB.evalSum ρ' obj = Sat.PB.coeffSumR obj := Sat.PB.evalSum_negate_eq ρ' obj
  simp only [Constr.sat, objVal] at h hle ⊢
  omega

/-- `OrdInv` carries over to a state with the same loaded order and objective
when the core-model property carries over. -/
theorem OrdInv_of {s s' : BoolCheckState} (h : OrdInv s) (hord : s'.ord = s.ord)
    (hobj : s'.curObj = s.curObj) (hoff : s'.curOffset = s.curOffset)
    (hcv : ∀ O z, s.ord = some (O, z) →
      CoreValidDB O z s.db s.coreIds (opbVal s.curObj s.curOffset) →
      CoreValidDB O z s'.db s'.coreIds (opbVal s.curObj s.curOffset)) :
    OrdInv s' := by
  intro O z hoz
  rw [hord] at hoz
  obtain ⟨hg, hl, ha, hc⟩ := h O z hoz
  refine ⟨hg, hl, ha, ?_⟩
  rw [hobj, hoff]
  exact coreValid_iff_DB.mpr (hcv O z hoz (coreValid_iff_DB.mp hc))

/-- `OrdInv` holds trivially when no order is loaded. -/
theorem OrdInv_of_none {s : BoolCheckState} (h : s.ord = none) : OrdInv s :=
  fun O z hoz => by rw [h] at hoz; cases hoz

theorem StoredGood_of {s s' : BoolCheckState} (h : s'.orders = s.orders)
    (hs : StoredGood s) : StoredGood s' := by
  intro p hp
  rw [h] at hp
  exact hs p hp

/-- The checker's top-level invariant: `DBOpt` and `BestWitnessed` carry the
theorems; `CoreImplied` justifies core-only `red` goals; `IdsBelowDb` says
the id counter is fresh (an insertion never overwrites a core constraint);
`StoredGood` and `OrdInv` are the order clauses (design §3: every stored
order is good, and `CoreValid` holds while an order is loaded). -/
def StateInv (s : BoolCheckState) : Prop :=
  DBOpt s.origConstrs s.objective s.offset s.best s.curObj s.curOffset s.db ∧
    BestWitnessed s.origConstrs s.objective s.offset s.bestWit ∧
    CoreImplied s ∧ IdsBelowDb s.db s.nextId ∧ StoredGood s ∧ OrdInv s

theorem DBOpt_insert_dbImplied {F : Array Constr} {obj : Objective}
    {offset : Int} {best : Option Int} {curObj : Objective} {curOffset : Int}
    {db : Std.HashMap Nat Constr} (id : Nat) (c : Constr)
    (h : DBOpt F obj offset best curObj curOffset db)
    (himpl : ∀ w, DBSatBy db w → c.sat w) :
    DBOpt F obj offset best curObj curOffset (db.insert id c) := by
  intro v hF himp
  obtain ⟨w, hw, hle⟩ := h v hF himp
  refine ⟨w, fun id' c' hget => ?_, hle⟩
  rw [HashMap_get?_insert] at hget
  by_cases heq : id == id'
  · simp [heq] at hget; subst hget; exact himpl w hw
  · simp [heq] at hget; exact hw id' c' hget

theorem DBOpt_erase_fold {F : Array Constr} {obj : Objective}
    {offset : Int} {best : Option Int} {curObj : Objective} {curOffset : Int}
    (db : Std.HashMap Nat Constr) (ids : List Nat)
    (h : DBOpt F obj offset best curObj curOffset db) :
    DBOpt F obj offset best curObj curOffset
      (ids.foldl (fun db id => db.erase id) db) := by
  intro v hF himp
  obtain ⟨w, hw, hle⟩ := h v hF himp
  exact ⟨w, DBSatBy_erase_fold db ids w hw, hle⟩

theorem Improving_updBest {obj : Objective} {offset : Int}
    (best : Option Int) (b' : Int) (v : Valuation)
    (h : Improving obj offset (updBest best b') v) :
    opbVal obj offset v < b' ∧ Improving obj offset best v := by
  cases best with
  | none =>
    exact ⟨h b' rfl, fun b hb => by cases hb⟩
  | some b =>
    have hmin := h (min b b') rfl
    refine ⟨by omega, fun b0 hb0 => ?_⟩
    cases hb0
    omega

theorem BestWitnessed_updBest {F : Array Constr} {obj : Objective}
    {offset : Int} (bestWit : Option Int) (ρ : Valuation)
    (hbw : BestWitnessed F obj offset bestWit) (hρ : FormulaSat F ρ) :
    BestWitnessed F obj offset (updBest bestWit (opbVal obj offset ρ)) := by
  intro b hb
  cases bestWit with
  | none =>
    simp only [updBest, Option.some.injEq] at hb
    exact ⟨ρ, hρ, hb⟩
  | some b0 =>
    simp only [updBest, Option.some.injEq] at hb
    by_cases hle : b0 ≤ opbVal obj offset ρ
    · obtain ⟨ρ0, h0, h0'⟩ := hbw b0 rfl
      exact ⟨ρ0, h0, by omega⟩
    · exact ⟨ρ, hρ, by omega⟩

/-- `updBestWit`: the witnessed value stays witnessed. -/
theorem BestWitnessed_updBestWit {F : Array Constr} {obj : Objective}
    {offset : Int} (chk : Bool) (bestWit : Option Int) (ρ : Valuation)
    (hbw : BestWitnessed F obj offset bestWit) (hρ : FormulaSat F ρ) :
    BestWitnessed F obj offset
      (updBestWit chk bestWit (opbVal obj offset ρ)) := by
  cases chk with
  | false => exact hbw
  | true => exact BestWitnessed_updBest bestWit ρ hbw hρ

theorem checkSolutionVals_sound (F : Array Constr) (obj curObj : Objective)
    (lits : List PBCatcher.OPBLit) (bo bc : Nat)
    (h : checkSolutionVals F obj curObj lits = some (bo, bc)) :
    ∃ ρ, FormulaSat F ρ ∧ objVal obj ρ = bo ∧ objVal curObj ρ = bc := by
  unfold checkSolutionVals at h
  split at h
  · cases h
  · rename_i pl _
    by_cases hf : formulaSatB F (solValuation pl) = true
    · simp only [hf, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      refine ⟨solValuation pl, fun c hc => ?_, h.1, h.2⟩
      have hc' := List.all_eq_true.mp hf c hc
      simpa [constrSatB, Constr.sat] using hc'
    · simp [hf] at h

/-- A valuation of objective value below `k` (`k ≤ coeffSum`) satisfies the
improvement constraint `obj ≤ k − 1`. -/
theorem improveConstr_sat_of_lt (obj : Objective) (k : Nat) (w : Valuation)
    (hk : k ≤ Sat.PB.coeffSumR obj) (h : objVal obj w < k) :
    (improveConstr obj k).sat w := by
  apply negate_sat_of_not_sat
  · exact hk
  · intro hs
    simp only [Constr.sat] at hs
    simp only [objVal] at h
    omega

/-- A valuation of OPB value below `v` satisfies the `obji v` constraint. -/
theorem objiConstr_sat_of_lt (obj : Objective) (offset v : Int)
    (w : Valuation) (h : opbVal obj offset w < v) :
    (objiConstr obj offset v).sat w := by
  have hle := Sat.PB.evalSum_le_coeffSumR w obj
  simp only [opbVal, objVal] at h
  show ((Sat.PB.coeffSumR obj : Int) + 1 + offset - v).toNat ≤
    Sat.PB.evalSum w (obj.map fun (a, l) => (a, l.negate))
  have heq : Sat.PB.evalSum w (obj.map fun (a, l) => (a, l.negate)) +
      Sat.PB.evalSum w obj = Sat.PB.coeffSumR obj :=
    Sat.PB.evalSum_negate_eq w obj
  generalize Sat.PB.evalSum w (obj.map fun (a, l) => (a, l.negate)) = n at heq ⊢
  omega

theorem checkSolution_sound (F : Array Constr) (obj : Objective)
    (lits : List PBCatcher.OPBLit) (b' : Nat)
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

theorem mkDBRec_lt (cs : List Constr) (startIdx : Nat) (id : Nat)
    (c : Constr) :
    (mkDBRec cs startIdx).get? id = some c → id < startIdx + cs.length := by
  induction cs generalizing startIdx with
  | nil =>
    simp only [mkDBRec]
    intro h; rw [HashMap_get?_empty] at h; cases h
  | cons hd tl ih =>
    simp only [mkDBRec]
    intro hget; rw [HashMap_get?_insert] at hget
    by_cases heq : startIdx == id
    · rw [beq_iff_eq] at heq; subst heq; simp
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hget
      have := ih (startIdx + 1) hget
      simp only [List.length_cons]; omega

/-! ### Dominance: soundness of `dom` -/

/-- The premises of a scope block hold at `v` (`none`: outside any scope, no
premises). -/
def ScopeCtx (sp : PBCatcher.ScopeKind → Option (List Constr)) :
    Option PBCatcher.ScopeKind → Valuation → Prop
  | none, _ => True
  | some k, v => ∀ prem, sp k = some prem → ∀ c ∈ prem, c.sat v

/-- The goals proved so far in a `dom` subproof hold at `v` under the
premises of the scope they were proved in, and the premises of the strict
goal are contradictory at `v` under those of its proof's scope. -/
def GoalsOk (sp : PBCatcher.ScopeKind → Option (List Constr)) (strictPrem : List Constr)
    (v : Valuation) (proved : List (String × Constr × Option PBCatcher.ScopeKind))
    (contras : List (Option PBCatcher.ScopeKind)) : Prop :=
  (∀ p ∈ proved, ScopeCtx sp p.2.2 v → p.2.1.sat v) ∧
    ∀ pv ∈ contras, ScopeCtx sp pv v → (∀ c ∈ strictPrem, c.sat v) → False

theorem DBSatBy_insertAll : ∀ (cs : List Constr) (db : Std.HashMap Nat Constr)
    (i : Nat) (v : Valuation), DBSatBy db v → (∀ c ∈ cs, c.sat v) →
    DBSatBy (insertAll db i cs) v
  | [], _, _, _, h, _ => h
  | c :: cs, db, i, v, h, hc => by
    simp only [insertAll]
    exact DBSatBy_insertAll cs _ (i + 1) v (DBSatBy_insert db i c v h (hc c List.mem_cons_self))
      (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc'))

/-- Soundness of one block of a `dom` subproof: if the block's premises hold
at `v` whenever its scope premises do, every goal it proves holds at `v`
under those scope premises (pointwise in `v`). -/
theorem processGoalItems_sound
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (goalOf : String → Option Constr) (strictId : String → Bool)
    (strictPrem : List Constr) (cur : Option PBCatcher.ScopeKind)
    (sp : PBCatcher.ScopeKind → Option (List Constr))
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v) :
    ∀ (items : List PBCatcher.ProofStep) (st : BoolCheckState)
      (proved : List (String × Constr × Option PBCatcher.ScopeKind))
      (contras : List (Option PBCatcher.ScopeKind)) (fin : BoolCheckState)
      (proved' : List (String × Constr × Option PBCatcher.ScopeKind))
      (contras' : List (Option PBCatcher.ScopeKind)),
      processGoalItems execFn goalOf strictId strictPrem cur st items proved contras =
        some (fin, proved', contras') →
      ∀ v, (ScopeCtx sp cur v → DBSatBy st.db v) →
      GoalsOk sp strictPrem v proved contras →
      GoalsOk sp strictPrem v proved' contras' ∧ (ScopeCtx sp cur v → DBSatBy fin.db v) := by
  intro items
  induction items with
  | nil =>
    intro st proved contras fin proved' contras' h v hv hp
    simp only [processGoalItems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hp, hv⟩
  | cons item rest ih =>
    intro st proved contras fin proved' contras' h v hv hp
    simp only [processGoalItems] at h
    split at h
    · rename_i gid steps hid
      by_cases hany : steps.any innerStepForbidden = true
      · rw [if_pos hany] at h; cases h
      rw [if_neg hany] at h
      have hls := lsteps_of_not_any steps hany
      by_cases hs : strictId gid = true
      · rw [if_pos hs] at h
        cases hx : execFn { st with db := insertAll st.db st.nextId strictPrem, nextId := st.nextId + strictPrem.length } steps.toList with
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
              refine ih _ _ _ fin proved' contras' h v hv ⟨hp.1, ?_⟩
              intro pv hpv
              rcases List.mem_cons.mp hpv with rfl | hpv
              · intro hctx hprem
                have hsub : DBSatBy (insertAll st.db st.nextId strictPrem) v :=
                  DBSatBy_insertAll _ _ _ v (hv hctx) hprem
                have hfin := hexec _ fin' steps.toList hls hx v hsub
                exact contra_unsat c v (by simpa [Constr.isContra] using hcon)
                  (hfin hid c (by rwa [Std.HashMap.get?_eq_getElem?]))
              · exact hp.2 pv hpv
            · rw [if_neg hcon] at h; cases h
      · rw [if_neg hs] at h
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
                refine ih _ _ _ fin proved' contras' h v hv ⟨?_, hp.2⟩
                intro p hpm
                rcases List.mem_cons.mp hpm with rfl | hpm
                · intro hctx
                  apply Classical.byContradiction
                  intro hn
                  have hsub : DBSatBy (st.db.insert st.nextId (negTriv G)) v :=
                    DBSatBy_insert _ _ _ v (hv hctx) (negTriv_sat_of_not_sat G v hn)
                  have hfin := hexec _ fin' steps.toList hls hx v hsub
                  exact contra_unsat c v (by simpa [Constr.isContra] using hcon)
                    (hfin hid c (by rwa [Std.HashMap.get?_eq_getElem?]))
                · exact hp.1 p hpm
              · rw [if_neg hcon] at h; cases h
    · split at h
      · rename_i hl
        cases hx : execFn st [item] with
        | none => rw [hx] at h; cases h
        | some st' =>
          rw [hx] at h
          simp only [] at h
          exact ih st' proved contras fin proved' contras' h v
            (fun hctx => hexec st st' [item] (by simpa using hl) hx v (hv hctx)) hp
      · cases h

/-- Soundness of the items of a `dom` subproof: for every model of the
subproof database, the proved goals hold under the premises of their scopes,
and the final database holds. -/
theorem processScopedItems_sound
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (goalOf : String → Option Constr) (strictId : String → Bool)
    (strictPrem : List Constr) (scopePrem : PBCatcher.ScopeKind → Option (List Constr))
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v) :
    ∀ (items : List PBCatcher.ProofStep) (st : BoolCheckState)
      (proved : List (String × Constr × Option PBCatcher.ScopeKind))
      (contras : List (Option PBCatcher.ScopeKind)) (fin : BoolCheckState)
      (proved' : List (String × Constr × Option PBCatcher.ScopeKind))
      (contras' : List (Option PBCatcher.ScopeKind)),
      processScopedItems execFn goalOf strictId strictPrem scopePrem st items proved
        contras = some (fin, proved', contras') →
      ∀ v, DBSatBy st.db v → GoalsOk scopePrem strictPrem v proved contras →
      GoalsOk scopePrem strictPrem v proved' contras' ∧ DBSatBy fin.db v := by
  intro items
  induction items with
  | nil =>
    intro st proved contras fin proved' contras' h v hv hp
    simp only [processScopedItems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hp, hv⟩
  | cons item rest ih =>
    intro st proved contras fin proved' contras' h v hv hp
    simp only [processScopedItems] at h
    split at h
    · rename_i kind sitems
      cases hsp : scopePrem kind with
      | none => rw [hsp] at h; cases h
      | some prem =>
        rw [hsp] at h
        simp only [] at h
        cases hx : processGoalItems execFn goalOf strictId strictPrem (some kind)
            { st with db := insertAll st.db st.nextId prem, nextId := st.nextId + prem.length } sitems.toList proved contras with
        | none => rw [hx] at h; cases h
        | some r =>
          obtain ⟨fin', proved'', contras''⟩ := r
          rw [hx] at h
          simp only [] at h
          have hblk := processGoalItems_sound execFn goalOf strictId strictPrem (some kind)
            scopePrem hexec _ _ _ _ _ _ _ hx v
            (fun hctx => DBSatBy_insertAll _ _ _ v hv (hctx prem hsp)) hp
          exact ih _ _ _ fin proved' contras' h v hv hblk.1
    · cases hx : processGoalItems execFn goalOf strictId strictPrem none st [item]
          proved contras with
      | none => rw [hx] at h; cases h
      | some r =>
        obtain ⟨st', proved'', contras''⟩ := r
        rw [hx] at h
        simp only [] at h
        have hblk := processGoalItems_sound execFn goalOf strictId strictPrem none
          scopePrem hexec _ _ _ _ _ _ _ hx v (fun _ => hv) hp
        exact ih _ _ _ fin proved' contras' h v (hblk.2 trivial) hblk.1

theorem processGoalItems_nextId_le
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (goalOf : String → Option Constr) (strictId : String → Bool)
    (strictPrem : List Constr) (cur : Option PBCatcher.ScopeKind)
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId) :
    ∀ (items : List PBCatcher.ProofStep) (st : BoolCheckState)
      (proved : List (String × Constr × Option PBCatcher.ScopeKind))
      (contras : List (Option PBCatcher.ScopeKind)) (fin : BoolCheckState)
      (proved' : List (String × Constr × Option PBCatcher.ScopeKind))
      (contras' : List (Option PBCatcher.ScopeKind)),
      processGoalItems execFn goalOf strictId strictPrem cur st items proved contras =
        some (fin, proved', contras') → st.nextId ≤ fin.nextId := by
  intro items
  induction items with
  | nil =>
    intro st proved contras fin proved' contras' h
    simp only [processGoalItems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Nat.le_refl _
  | cons item rest ih =>
    intro st proved contras fin proved' contras' h
    simp only [processGoalItems] at h
    split at h
    · rename_i gid steps hid
      by_cases hany : steps.any innerStepForbidden = true
      · rw [if_pos hany] at h; cases h
      rw [if_neg hany] at h
      have hls := lsteps_of_not_any steps hany
      by_cases hs : strictId gid = true
      · rw [if_pos hs] at h
        cases hx : execFn { st with db := insertAll st.db st.nextId strictPrem, nextId := st.nextId + strictPrem.length } steps.toList with
        | none => rw [hx] at h; cases h
        | some fin' =>
          rw [hx] at h
          simp only [] at h
          have h1 := hmono _ fin' steps.toList hls hx
          cases hc : fin'.db[hid]? with
          | none => rw [hc] at h; cases h
          | some c =>
            rw [hc] at h
            simp only [] at h
            by_cases hcon : c.isContra = true
            · rw [if_pos hcon] at h
              have h2 := ih _ _ _ fin proved' contras' h
              simp only [] at h1 h2
              omega
            · rw [if_neg hcon] at h; cases h
      · rw [if_neg hs] at h
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
            have h1 := hmono _ fin' steps.toList hls hx
            cases hc : fin'.db[hid]? with
            | none => rw [hc] at h; cases h
            | some c =>
              rw [hc] at h
              simp only [] at h
              by_cases hcon : c.isContra = true
              · rw [if_pos hcon] at h
                have h2 := ih _ _ _ fin proved' contras' h
                simp only [] at h1 h2
                omega
              · rw [if_neg hcon] at h; cases h
    · split at h
      · rename_i hl
        cases hx : execFn st [item] with
        | none => rw [hx] at h; cases h
        | some st' =>
          rw [hx] at h
          simp only [] at h
          exact Nat.le_trans (hmono st st' [item] (by simpa using hl) hx)
            (ih st' proved contras fin proved' contras' h)
      · cases h

theorem processScopedItems_nextId_le
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (goalOf : String → Option Constr) (strictId : String → Bool)
    (strictPrem : List Constr) (scopePrem : PBCatcher.ScopeKind → Option (List Constr))
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId) :
    ∀ (items : List PBCatcher.ProofStep) (st : BoolCheckState)
      (proved : List (String × Constr × Option PBCatcher.ScopeKind))
      (contras : List (Option PBCatcher.ScopeKind)) (fin : BoolCheckState)
      (proved' : List (String × Constr × Option PBCatcher.ScopeKind))
      (contras' : List (Option PBCatcher.ScopeKind)),
      processScopedItems execFn goalOf strictId strictPrem scopePrem st items proved
        contras = some (fin, proved', contras') → st.nextId ≤ fin.nextId := by
  intro items
  induction items with
  | nil =>
    intro st proved contras fin proved' contras' h
    simp only [processScopedItems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Nat.le_refl _
  | cons item rest ih =>
    intro st proved contras fin proved' contras' h
    simp only [processScopedItems] at h
    split at h
    · rename_i kind sitems
      cases hsp : scopePrem kind with
      | none => rw [hsp] at h; cases h
      | some prem =>
        rw [hsp] at h
        simp only [] at h
        cases hx : processGoalItems execFn goalOf strictId strictPrem (some kind)
            { st with db := insertAll st.db st.nextId prem, nextId := st.nextId + prem.length } sitems.toList proved contras with
        | none => rw [hx] at h; cases h
        | some r =>
          obtain ⟨fin', proved'', contras''⟩ := r
          rw [hx] at h
          simp only [] at h
          have h1 := processGoalItems_nextId_le execFn goalOf strictId strictPrem _ hmono
            _ _ _ _ _ _ _ hx
          have h2 := ih _ _ _ fin proved' contras' h
          simp only [] at h1 h2
          omega
    · cases hx : processGoalItems execFn goalOf strictId strictPrem none st [item]
          proved contras with
      | none => rw [hx] at h; cases h
      | some r =>
        obtain ⟨st', proved'', contras''⟩ := r
        rw [hx] at h
        simp only [] at h
        exact Nat.le_trans (processGoalItems_nextId_le execFn goalOf strictId strictPrem
          _ hmono _ _ _ _ _ _ _ hx) (ih _ _ _ fin proved' contras' h)

theorem provLeqOk_ctx {sp : PBCatcher.ScopeKind → Option (List Constr)}
    {pv : Option PBCatcher.ScopeKind} {v : Valuation} (h : provLeqOk pv = true)
    (hctx : ScopeCtx sp (some .leq) v) : ScopeCtx sp pv v := by
  cases pv with
  | none => trivial
  | some k =>
    cases k with
    | leq => exact hctx
    | geq => simp [provLeqOk] at h

theorem provGeqOk_ctx {sp : PBCatcher.ScopeKind → Option (List Constr)}
    {pv : Option PBCatcher.ScopeKind} {v : Valuation} (h : provGeqOk pv = true)
    (hctx : ScopeCtx sp (some .geq) v) : ScopeCtx sp pv v := by
  cases pv with
  | none => trivial
  | some k =>
    cases k with
    | geq => exact hctx
    | leq => simp [provGeqOk] at h

theorem domHashCovered_sound (nC : Constr)
    (proved : List (String × Constr × Option PBCatcher.ScopeKind)) (gid : String)
    (G : Constr) (v : Valuation) (h : domHashCovered nC proved gid G = true)
    (hnC : nC.sat v) (hp : ∀ p ∈ proved, provLeqOk p.2.2 = true → p.2.1.sat v) :
    G.sat v := by
  unfold domHashCovered at h
  simp only [Bool.or_eq_true] at h
  rcases h with (htr | hpr) | himp
  · exact trivialByPair_sat _ v htr
  · obtain ⟨p, hpm, hpc⟩ := List.any_eq_true.mp hpr
    simp only [Bool.and_eq_true] at hpc
    exact constrMatchNorm_sat _ _ v hpc.2 (hp p hpm hpc.1.2)
  · exact impliesSyntactic_sound _ _ v himp hnC

theorem domOrderGoalsCovered_sound (nC : Constr)
    (proved : List (String × Constr × Option PBCatcher.ScopeKind)) (v : Valuation)
    (hnC : nC.sat v) (hp : ∀ p ∈ proved, provLeqOk p.2.2 = true → p.2.1.sat v) :
    ∀ (j : Nat) (gs : List Constr), domOrderGoalsCovered nC proved j gs = true →
      ∀ G ∈ gs, G.sat v
  | _, [], _ => by simp
  | j, G :: gs, h => by
    simp only [domOrderGoalsCovered, Bool.and_eq_true] at h
    intro G' hG'
    rcases List.mem_cons.mp hG' with rfl | hG'
    · exact domHashCovered_sound nC proved _ _ v h.1 hnC hp
    · exact domOrderGoalsCovered_sound nC proved v hnC hp (j + 1) gs h.2 G' hG'

/-- A covered core goal of a `dom` step holds after applying the witness. -/
theorem dbGoalCoveredDom_sound (subst : List (Nat × Sat.PB.SubstVal))
    (nC : Constr) (goalDb lookupDb : Std.HashMap Nat Constr)
    (proved : List (String × Constr × Option PBCatcher.ScopeKind)) (D : Constr)
    (w : Valuation) (h : dbGoalCoveredDom subst nC goalDb lookupDb proved D = true)
    (hdb : DBSatBy lookupDb w) (hD : D.sat w) (hnC : nC.sat w)
    (hp : ∀ p ∈ proved, provLeqOk p.2.2 = true → p.2.1.sat w) :
    D.sat (Sat.PB.applyValuation subst w) := by
  unfold dbGoalCoveredDom at h
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
    exact constrMatchNorm_sat _ _ w hpc.2 (hp p hpm hpc.1.1)
  · exact constrInDB_sat _ lookupDb w hin hdb

theorem varsOf_free_of_termsAuxFree {A : List Nat} {c : Constr}
    (h : termsAuxFree A c.terms = true) :
    ∀ x ∈ Sat.PB.Dominance.varsOf c, x ∉ A := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  unfold termsAuxFree at h
  exact of_decide_eq_true (List.all_eq_true.mp h t ht)

theorem rupNegate_auxFree {A : List Nat} {C : Constr}
    (h : termsAuxFree A (PBCatcher.normalizeConstr C).terms = true) :
    ∀ x ∈ Sat.PB.Dominance.varsOf (rupNegate C), x ∉ A := by
  have key : (rupNegate C).terms = (PBCatcher.normalizeConstr C).negate.terms := by
    unfold rupNegate
    dsimp only
    split <;> rfl
  intro x hx
  unfold Sat.PB.Dominance.varsOf at hx
  rw [key] at hx
  simp only [Constr.negate, List.map_map] at hx
  obtain ⟨⟨a, l⟩, ht, rfl⟩ := List.mem_map.mp hx
  unfold termsAuxFree at h
  have := of_decide_eq_true (List.all_eq_true.mp h (a, l) ht)
  cases l <;> exact this

theorem lookupSubst_mem {x : Nat} {sv : Sat.PB.SubstVal} :
    ∀ {ω : List (Nat × Sat.PB.SubstVal)}, Sat.PB.lookupSubst ω x = some sv →
      ∃ y, (y, sv) ∈ ω
  | [], h => by simp [Sat.PB.lookupSubst] at h
  | (y, sv') :: rest, h => by
    simp only [Sat.PB.lookupSubst] at h
    split at h
    · cases h; exact ⟨y, List.mem_cons_self⟩
    · obtain ⟨y', hy'⟩ := lookupSubst_mem h
      exact ⟨y', List.mem_cons_of_mem _ hy'⟩

theorem imgFree_of_substAuxFree {A : List Nat} {ω : List (Nat × Sat.PB.SubstVal)}
    (h : substAuxFree A ω = true) (x : Nat) : Sat.PB.Dominance.ImgFree ω A x := by
  intro sv hsv j hj
  obtain ⟨y, hy⟩ := lookupSubst_mem hsv
  unfold substAuxFree at h
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h (y, sv) hy) j hj)

theorem mem_dbList_filter {db : Std.HashMap Nat Constr} {p : Nat → Constr → Bool}
    {c : Constr} (h : c ∈ dbList (db.filter p)) : c ∈ dbList db := by
  obtain ⟨⟨id, c'⟩, hmem, rfl⟩ := List.mem_map.mp h
  have hget := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem
  rw [Std.HashMap.getElem?_filter', Option.filter_eq_some_iff] at hget
  exact List.mem_map.mpr ⟨(id, c'), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget.1, rfl⟩

theorem mem_coreList_dbList {db : Std.HashMap Nat Constr} {core : Std.HashSet Nat}
    {c : Constr} (h : c ∈ coreList db core) : c ∈ dbList db :=
  mem_dbList_filter h

theorem dbList_auxFree {A : List Nat} {db : Std.HashMap Nat Constr}
    (h : db.toList.all (fun p => termsAuxFree A p.2.terms) = true) :
    ∀ c ∈ dbList db, ∀ x ∈ Sat.PB.Dominance.varsOf c, x ∉ A := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  exact varsOf_free_of_termsAuxFree (List.all_eq_true.mp h p hp)

/-- The objective goal before normalization (`objGoalConstr` normalizes it). -/
def objGoalRaw (subst : List (Nat × Sat.PB.SubstVal)) (obj : Objective) : Constr :=
  let s := Sat.PB.applySubstConstr subst
    ⟨obj.map (fun (a, l) => (a, l.negate)), Sat.PB.coeffSumR obj⟩
  ⟨obj ++ s.terms, s.degree⟩

theorem objGoalConstr_eq (subst : List (Nat × Sat.PB.SubstVal)) (obj : Objective) :
    objGoalConstr subst obj = PBCatcher.normalizeConstr (objGoalRaw subst obj) := rfl

theorem objGoalRaw_auxFree {A : List Nat} {subst : List (Nat × Sat.PB.SubstVal)}
    {obj : Objective} (h3 : termsAuxFree A obj = true)
    (h4 : ∀ x, Sat.PB.Dominance.ImgFree subst A x) :
    ∀ x ∈ Sat.PB.Dominance.varsOf (objGoalRaw subst obj), x ∉ A := by
  have hobj : ∀ x ∈ Sat.PB.Dominance.varsOf (⟨obj, 0⟩ : Constr), x ∉ A :=
    varsOf_free_of_termsAuxFree h3
  have hneg : ∀ x ∈ Sat.PB.Dominance.varsOf
      (⟨obj.map (fun (a, l) => (a, l.negate)), Sat.PB.coeffSumR obj⟩ : Constr), x ∉ A := by
    intro x hx
    unfold Sat.PB.Dominance.varsOf at hx
    simp only [List.map_map] at hx
    obtain ⟨⟨a, l⟩, ht, rfl⟩ := List.mem_map.mp hx
    have := hobj l.var (List.mem_map.mpr ⟨(a, l), ht, rfl⟩)
    cases l <;> exact this
  have hs := Sat.PB.Dominance.varsOf_applySubstConstr_free hneg (fun x _ => h4 x)
  intro x hx
  unfold objGoalRaw Sat.PB.Dominance.varsOf at hx
  simp only [List.map_append, List.mem_append] at hx
  rcases hx with hx | hx
  · exact hobj x hx
  · exact hs x hx

/-- Soundness of the dominance check (`checkDominance`, design T3 with the
bridges T7): with the loaded order good, its literals fitting it, the aux
variables fresh (`domFresh`) and `CoreValid` before the step, `CoreValid`
holds with `C` (normalized) added to the database. With `qed : cid`, `C` is
implied by the database; otherwise the checked goals give, for every model
`ρ` of the database falsifying `C`: `ρ∘ω` satisfies the core (core goals,
with `specElim` for those proved in `scope leq`), `ρ∘ω ⪯ ρ` (order goals,
`ordLeq_of_goal`), `¬ ρ ⪯ ρ∘ω` (strict goal, `ordStrict_of_goal`) and the
objective does not grow (objective goal), and `coreValid_dom` applies. -/
theorem checkDominance_sound
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (st0 : BoolCheckState) (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (qedHint : Option Nat) (fid : Nat)
    (h : checkDominance execFn st0 O z subst C items qedHint = some fid)
    (hgood : Sat.PB.Dominance.GoodOrder O) (hz : z.length = O.left.length)
    (hzaux : ∀ l ∈ z, l.var ∉ O.aux)
    (hfresh : domFresh O.aux st0.db (PBCatcher.normalizeConstr C) st0.curObj subst = true)
    (hcv : Sat.PB.Dominance.CoreValid O z (coreList st0.db st0.coreIds) (dbList st0.db)
      (opbVal st0.curObj st0.curOffset)) :
    Sat.PB.Dominance.CoreValid O z (coreList st0.db st0.coreIds)
      (PBCatcher.normalizeConstr C :: dbList st0.db) (opbVal st0.curObj st0.curOffset) := by
  simp only [domFresh, Bool.and_eq_true] at hfresh
  obtain ⟨⟨⟨hF1, hF2⟩, hF3⟩, hF4⟩ := hfresh
  have himg' : ∀ x, Sat.PB.Dominance.ImgFree subst O.aux x := imgFree_of_substAuxFree hF4
  have himg : ∀ l ∈ z, Sat.PB.Dominance.ImgFree subst O.aux l.var := fun l _ => himg' l.var
  have hGaux : ∀ g ∈ rupNegate C :: dbList st0.db, ∀ x ∈ Sat.PB.Dominance.varsOf g,
      x ∉ O.aux := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact rupNegate_auxFree hF2
    · exact dbList_auxFree hF1 g hg
  unfold checkDominance at h
  dsimp only at h
  cases hp : processScopedItems execFn (domGoalOf O z subst st0.curObj (fun n => st0.db[n]?))
      (domStrictId O.defs.length)
      (O.defs.map (substGoal (Sat.PB.Dominance.sigmaGeq O z subst)))
      (domScopePrem O z subst)
      { st0 with db := st0.db.insert st0.nextId (rupNegate C), nextId := st0.nextId + 1 }
      items [] [] with
  | none => rw [hp] at h; cases h
  | some r =>
    obtain ⟨fin, proved, contras⟩ := r
    rw [hp] at h
    dsimp only at h
    have hok : ∀ v, DBSatBy st0.db v → (rupNegate C).sat v →
        GoalsOk (domScopePrem O z subst)
          (O.defs.map (substGoal (Sat.PB.Dominance.sigmaGeq O z subst))) v proved contras ∧
        DBSatBy fin.db v := fun v hv hn =>
      processScopedItems_sound execFn _ _ _ _ hexec items _ [] [] fin proved contras hp v
        (DBSatBy_insert _ _ _ v hv hn) ⟨by simp, by simp⟩
    cases qedHint with
    | some cid =>
      apply Sat.PB.Dominance.coreValid_cons_implied _ hcv
      intro ρ hρ
      have hdb := (forall_dbList_iff _ ρ).mp hρ
      apply normalize_sat
      apply Classical.byContradiction
      intro hC
      have hfin := (hok ρ hdb (rupNegate_sat_of_not_sat C ρ hC)).2
      cases hc : fin.db[cid]? with
      | none => simp [hc] at h
      | some c =>
        by_cases hcon : c.isContra = true
        · exact contra_unsat c ρ (by simpa [Constr.isContra] using hcon)
            (hfin cid c (by rwa [Std.HashMap.get?_eq_getElem?]))
        · simp [hc, hcon] at h
    | none =>
      dsimp only at h
      split at h
      · rename_i hall
        simp only [Bool.and_eq_true] at hall
        obtain ⟨⟨⟨hord, hstrict⟩, hobj⟩, hcore⟩ := hall
        -- goals proved outside any scope or in `scope leq` hold under `Spec[σ≤]`
        have hleq : ∀ ρ', (∀ g ∈ rupNegate C :: dbList st0.db, g.sat ρ') →
            (∀ s ∈ O.spec, (Sat.PB.applySubstConstr
              (Sat.PB.Dominance.sigmaLeq O z subst) s).sat ρ') →
            ∀ p ∈ proved, provLeqOk p.2.2 = true → p.2.1.sat ρ' := by
          intro ρ' hG hS p hpm hpk
          obtain ⟨hnC', hdb'⟩ := List.forall_mem_cons.mp hG
          have hgo := (hok ρ' ((forall_dbList_iff _ ρ').mp hdb') hnC').1
          apply hgo.1 p hpm
          apply provLeqOk_ctx hpk
          intro prem hprem c hc
          simp only [domScopePrem, Option.some.injEq] at hprem
          subst hprem
          exact substGoal_map_sat hS c hc
        apply Sat.PB.Dominance.coreValid_dom hgood.trans hcv
        intro ρ hρB hρC
        have hnC : (rupNegate C).sat ρ :=
          rupNegate_sat_of_not_sat C ρ (fun hc => hρC (normalize_sat C ρ hc))
        have hGρ : ∀ g ∈ rupNegate C :: dbList st0.db, g.sat ρ :=
          List.forall_mem_cons.mpr ⟨hnC, hρB⟩
        -- g1: core goals (`specElim_leq` over all of them)
        have hHaux : ∀ hc ∈ (coreList st0.db st0.coreIds).map
            (Sat.PB.applySubstConstr subst), ∀ x ∈ Sat.PB.Dominance.varsOf hc,
            x ∉ O.aux := by
          intro hc hmem
          obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hmem
          exact Sat.PB.Dominance.varsOf_applySubstConstr_free
            (dbList_auxFree hF1 D (mem_coreList_dbList hD)) (fun x _ => himg' x)
        have hel := Sat.PB.Dominance.specElim_leq
          (H := (coreList st0.db st0.coreIds).map (Sat.PB.applySubstConstr subst))
          hgood.wf hgood.vars hgood.isSpec hz hzaux himg hGaux hHaux
          (fun ρ' hG hS hc hmem => by
            obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hmem
            obtain ⟨hnC', hdb'⟩ := List.forall_mem_cons.mp hG
            have hdbρ := (forall_dbList_iff _ ρ').mp hdb'
            obtain ⟨⟨id, D'⟩, hmemt, rfl⟩ := List.mem_map.mp hD
            have hcov := List.all_eq_true.mp hcore (id, D') hmemt
            exact Sat.PB.applySubstConstr_sound subst _ ρ'
              (dbGoalCoveredDom_sound subst _ _ st0.db proved D' ρ' hcov hdbρ
                (hdb' _ (mem_coreList_dbList hD)) hnC' (hleq ρ' hG hS)))
          ρ hGρ
        have g1 : ∀ d ∈ coreList st0.db st0.coreIds,
            d.sat (Sat.PB.applyValuation subst ρ) := fun d hd =>
          Sat.PB.applySubstConstr_sat_rev subst d ρ (hel _ (List.mem_map.mpr ⟨d, hd, rfl⟩))
        -- g2: order goals
        have g2 := Sat.PB.Dominance.ordLeq_of_goal (G := rupNegate C :: dbList st0.db)
          hgood.wf hgood.vars hgood.isSpec hz hzaux himg hGaux
          (fun ρ' hG hS d hd => by
            have := domOrderGoalsCovered_sound (rupNegate C) proved ρ'
              (List.forall_mem_cons.mp hG).1 (hleq ρ' hG hS) 1 _ hord
            exact normalize_sat_rev _ ρ' (this _ (List.mem_map.mpr ⟨d, hd, rfl⟩)))
          ρ hGρ
        -- g3: the strict goal
        obtain ⟨pv, hpv, hpvk⟩ := List.any_eq_true.mp hstrict
        have g3 := Sat.PB.Dominance.ordStrict_of_goal (G := rupNegate C :: dbList st0.db)
          hgood.wf hgood.vars hz hzaux himg hGaux
          (fun ρ' hG hS hD => by
            obtain ⟨hnC', hdb'⟩ := List.forall_mem_cons.mp hG
            have hgo := (hok ρ' ((forall_dbList_iff _ ρ').mp hdb') hnC').1
            apply hgo.2 pv hpv
            · apply provGeqOk_ctx hpvk
              intro prem hprem c hc
              simp only [domScopePrem, Option.some.injEq] at hprem
              subst hprem
              exact substGoal_map_sat hS c hc
            · exact substGoal_map_sat hD)
          ρ hGρ
        -- g4: the objective goal
        have g4 : opbVal st0.curObj st0.curOffset (Sat.PB.applyValuation subst ρ) ≤
            opbVal st0.curObj st0.curOffset ρ := by
          unfold domObjCovered at hobj
          simp only [Bool.or_eq_true, Bool.not_eq_true'] at hobj
          rcases hobj with hna | hcov
          · simp only [opbVal, objVal]
            rw [Sat.PB.evalSum_applyValuation_noSubst subst ρ _ hna]
            exact Int.le_refl _
          · have helo := Sat.PB.Dominance.specElim_leq (H := [objGoalRaw subst st0.curObj])
              hgood.wf hgood.vars hgood.isSpec hz hzaux himg hGaux
              (fun hc hmem => by
                rw [List.mem_singleton] at hmem
                subst hmem
                exact objGoalRaw_auxFree hF3 himg')
              (fun ρ' hG hS hc hmem => by
                rw [List.mem_singleton] at hmem
                subst hmem
                have := domHashCovered_sound _ proved _ _ ρ' hcov
                  (List.forall_mem_cons.mp hG).1 (hleq ρ' hG hS)
                rw [objGoalConstr_eq] at this
                exact normalize_sat_rev _ ρ' this)
              ρ hGρ _ (List.mem_singleton_self _)
            have := objGoalConstr_sound subst st0.curObj ρ
              (by rw [objGoalConstr_eq]; exact normalize_sat _ ρ helo)
            simp only [opbVal]
            omega
        exact ⟨g1, g2, g3, g4⟩
      · cases h

theorem checkDominance_nextId_lt
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId)
    (st0 : BoolCheckState) (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (qedHint : Option Nat) (fid : Nat)
    (h : checkDominance execFn st0 O z subst C items qedHint = some fid) :
    st0.nextId < fid := by
  unfold checkDominance at h
  dsimp only at h
  cases hp : processScopedItems execFn (domGoalOf O z subst st0.curObj (fun n => st0.db[n]?))
      (domStrictId O.defs.length)
      (O.defs.map (substGoal (Sat.PB.Dominance.sigmaGeq O z subst)))
      (domScopePrem O z subst)
      { st0 with db := st0.db.insert st0.nextId (rupNegate C), nextId := st0.nextId + 1 }
      items [] [] with
  | none => rw [hp] at h; cases h
  | some r =>
    obtain ⟨fin, proved, contras⟩ := r
    rw [hp] at h
    dsimp only at h
    have h1 := processScopedItems_nextId_le execFn _ _ _ _ hmono items _ [] [] fin proved
      contras hp
    simp only [] at h1
    have key : ∀ b : Bool, (if b = true then some fin.nextId else none) =
        some fid → st0.nextId < fid := by
      intro b hb
      cases b
      · simp at hb
      · simp only [ite_true, Option.some.injEq] at hb; omega
    exact key _ h

/-- A `dom` step: the objective fields are unchanged, `C` (normalized) is
inserted at an id `fid` at or above the old counter (into the core iff
`strengthening_to_core`), every model of the old database has a model of the
new one that is at least as good (the transport condition of `DBOpt`), and
`OrdInv` holds afterwards. -/
theorem domStep_spec
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId)
    (state : BoolCheckState) (constr : PBCatcher.OPBConstr)
    (substPairs : List (String × String)) (items : List PBCatcher.ProofStep)
    (qedHint : Option Nat) (st' : BoolCheckState)
    (hib : IdsBelowDb state.db state.nextId) (hoi : OrdInv state)
    (h : domStep execFn state constr substPairs items qedHint = some st') :
    SameObjFields st' state ∧
    (∃ fid C', state.nextId ≤ fid ∧ st'.db = state.db.insert fid C' ∧
      st'.nextId = fid + 1 ∧
      st'.coreIds = (if state.s2c then state.coreIds.insert fid else state.coreIds) ∧
      st'.s2c = state.s2c ∧ st'.ord = state.ord ∧ st'.orders = state.orders) ∧
    (∀ w, DBSatBy state.db w → ∃ w', DBSatBy st'.db w' ∧
      opbVal st'.curObj st'.curOffset w' ≤ opbVal state.curObj state.curOffset w) ∧
    OrdInv st' := by
  unfold domStep at h
  split at h
  · cases h
  · rename_i O z hord
    split at h
    · cases h
    · rename_i C _
      split at h
      · cases h
      · rename_i subst _
        split at h
        · cases h
        · rename_i hfr
          have hfresh : domFresh O.aux state.db (PBCatcher.normalizeConstr C) state.curObj
              subst = true := by simpa using hfr
          split at h
          · cases h
          · rename_i fid hchk
            cases h
            have hlt := checkDominance_nextId_lt execFn hmono _ _ _ _ _ _ _ fid hchk
            have hk : state.db.get? fid = none := IdsBelowDb_fresh hib (Nat.le_of_lt hlt)
            obtain ⟨hgood, hz, hzaux, hcv⟩ := hoi O z hord
            have hcv' := checkDominance_sound execFn hexec state O z subst C items qedHint
              fid hchk hgood hz hzaux hfresh hcv
            -- models of the new database from the extended `CoreValid`
            have hnew : ∀ ρ, CoreSatBy state.db state.coreIds ρ → ∃ ρ',
                DBSatBy (state.db.insert fid (PBCatcher.normalizeConstr C)) ρ' ∧
                Sat.PB.Dominance.Leq O z ρ' ρ ∧
                opbVal state.curObj state.curOffset ρ' ≤
                  opbVal state.curObj state.curOffset ρ := by
              intro ρ hρ
              obtain ⟨ρ', h1, h2, h3⟩ := hcv' ρ ((forall_coreList_iff _ _ ρ).mpr hρ)
              obtain ⟨hc, hB⟩ := List.forall_mem_cons.mp h1
              exact ⟨ρ', DBSatBy_insert _ _ _ ρ' ((forall_dbList_iff _ ρ').mp hB) hc, h2, h3⟩
            refine ⟨⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩,
              ⟨fid, _, Nat.le_of_lt hlt, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
            · intro w hw
              obtain ⟨w', h1, _, h3⟩ := hnew w (CoreSatBy_of_DBSatBy hw)
              exact ⟨w', h1, h3⟩
            · intro O' z' hoz
              have hoz' : state.ord = some (O', z') := hoz
              rw [hord] at hoz'
              cases hoz'
              refine ⟨hgood, hz, hzaux, ?_⟩
              apply coreValid_iff_DB.mpr
              intro ρ hρ
              have hsub : ∀ id, state.coreIds.contains id = true →
                  (if state.s2c then state.coreIds.insert fid else state.coreIds).contains id =
                    true := by
                intro id hid
                split
                · rw [Std.HashSet.contains_insert, hid, Bool.or_true]
                · exact hid
              exact hnew ρ (CoreSatBy_of_insert_fresh hk hsub hρ)

/-! ### Redundance under a loaded order: soundness of `red` and checked `delc` -/

/-- Without scope premises every scope context holds. -/
theorem ScopeCtx_none {pv : Option PBCatcher.ScopeKind} {v : Valuation} :
    ScopeCtx (fun _ => none) pv v := by
  cases pv with
  | none => trivial
  | some _ => intro prem hp; cases hp

theorem leqProved_sat {proved : List (String × Constr × Option PBCatcher.ScopeKind)}
    {v : Valuation} (h : ∀ p ∈ proved, provLeqOk p.2.2 = true → p.2.1.sat v) :
    ∀ p ∈ leqProved proved, p.2.sat v := by
  intro p hp
  unfold leqProved at hp
  obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp hp
  by_cases hk : provLeqOk q.2.2 = true
  · rw [if_pos hk] at hqe
    cases hqe
    exact h q hq hk
  · rw [if_neg hk] at hqe; cases hqe

theorem mem_dbList_of_get? {db : Std.HashMap Nat Constr} {id : Nat} {c : Constr}
    (h : db.get? id = some c) : c ∈ dbList db := by
  rw [Std.HashMap.get?_eq_getElem?] at h
  exact List.mem_map.mpr ⟨(id, c), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h, rfl⟩

/-- A redundance check under a loaded order closed by `qed : cid` is an
implication proof: every model of the subproof database satisfies `C`. -/
theorem checkRedOrder_qed_implied
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (st0 : BoolCheckState) (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal)
    (goalDb lookupDb freshDb : Std.HashMap Nat Constr)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (cid fid : Nat)
    (h : checkRedOrder execFn st0 O z goalDb lookupDb freshDb subst C items (some cid) =
      some fid) :
    ∀ w, DBSatBy st0.db w → C.sat w := by
  intro w hw
  apply Classical.byContradiction
  intro hC
  have hw1 : DBSatBy (st0.db.insert st0.nextId (rupNegate C)) w :=
    DBSatBy_insert _ _ _ w hw (rupNegate_sat_of_not_sat C w hC)
  unfold checkRedOrder at h
  split at h
  · cases h
  dsimp only at h
  generalize (if hasScope items = true then redScopePrem O z subst
    else fun _ => none) = sp at h
  cases hp : processScopedItems execFn
      (redOrdGoalOf O z subst C st0.curObj (fun n => lookupDb[n]?)) (fun _ => false) []
      sp { st0 with db := st0.db.insert st0.nextId (rupNegate C), nextId := st0.nextId + 1 }
      items [] [] with
  | none => rw [hp] at h; cases h
  | some r =>
    obtain ⟨fin, proved, contras⟩ := r
    rw [hp] at h
    dsimp only at h
    have hfin := (processScopedItems_sound execFn _ _ _ _ hexec items _ [] [] fin proved
      contras hp w hw1 ⟨by simp, by simp⟩).2
    cases hc : fin.db[cid]? with
    | none => simp [hc] at h
    | some c =>
      by_cases hcon : c.isContra = true
      · exact contra_unsat c w (by simpa [Constr.isContra] using hcon)
          (hfin cid c (by rwa [Std.HashMap.get?_eq_getElem?]))
      · simp [hc, hcon] at h

/-- Soundness of the redundance check under a loaded order (`checkRedOrder`,
design T4/T5 with the bridges T7): for every model `w` of the subproof
database that falsifies `C`, `w∘ω` satisfies `C` and `goalDb`, the objective
does not grow, and `w∘ω ⪯ w` in the loaded order. Goals proved in `scope leq`
are transferred to `w` by `specElim_leq` (the aux variables are fresh then);
`w∘ω ⪯ w` comes from the order goals (`ordLeq_of_goal`) or, when `ω` does not
touch the loaded literals, from reflexivity (`leq_of_untouched`). `freshDb`
contains the subproof database and `goalDb`. -/
theorem checkRedOrder_sound
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (st0 : BoolCheckState) (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal)
    (goalDb lookupDb freshDb : Std.HashMap Nat Constr)
    (hgoal : ∀ v, DBSatBy st0.db v → DBSatBy goalDb v)
    (hlook : ∀ v, DBSatBy st0.db v → DBSatBy lookupDb v)
    (hdbF : ∀ c ∈ dbList st0.db, c ∈ dbList freshDb)
    (hgF : ∀ c ∈ dbList goalDb, c ∈ dbList freshDb)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (qedHint : Option Nat) (fid : Nat)
    (h : checkRedOrder execFn st0 O z goalDb lookupDb freshDb subst C items qedHint =
      some fid)
    (hgood : Sat.PB.Dominance.GoodOrder O) (hz : z.length = O.left.length)
    (hzaux : ∀ l ∈ z, l.var ∉ O.aux)
    (w : Valuation) (hw : DBSatBy st0.db w) (hC : ¬ C.sat w) :
    C.sat (Sat.PB.applyValuation subst w) ∧
      DBSatBy goalDb (Sat.PB.applyValuation subst w) ∧
      objVal st0.curObj (Sat.PB.applyValuation subst w) ≤ objVal st0.curObj w ∧
      Sat.PB.Dominance.Leq O z (Sat.PB.applyValuation subst w) w := by
  have hq : qedHint = none := by
    cases qedHint with
    | none => rfl
    | some cid =>
      exact absurd (checkRedOrder_qed_implied execFn hexec st0 O z goalDb lookupDb freshDb
        subst C items cid fid h w hw) hC
  subst hq
  have hnC : (rupNegate C).sat w := rupNegate_sat_of_not_sat C w hC
  unfold checkRedOrder at h
  split at h
  · cases h
  rename_i hfr
  dsimp only at h
  generalize hsp : (if hasScope items = true then redScopePrem O z subst
    else fun _ => none) = sp at h
  cases hp : processScopedItems execFn
      (redOrdGoalOf O z subst C st0.curObj (fun n => lookupDb[n]?)) (fun _ => false) []
      sp { st0 with db := st0.db.insert st0.nextId (rupNegate C), nextId := st0.nextId + 1 }
      items [] [] with
  | none => rw [hp] at h; cases h
  | some r =>
    obtain ⟨fin, proved, contras⟩ := r
    rw [hp] at h
    dsimp only at h
    split at h
    · rename_i hall
      simp only [Bool.and_eq_true] at hall
      obtain ⟨⟨⟨h1, hord⟩, hobj⟩, hdbg⟩ := hall
      have hok : ∀ v, DBSatBy st0.db v → (rupNegate C).sat v →
          GoalsOk sp [] v proved contras := fun v hv hn =>
        (processScopedItems_sound execFn _ _ _ _ hexec items _ [] [] fin proved contras hp v
          (DBSatBy_insert _ _ _ v hv hn) ⟨by simp, by simp⟩).1
      -- the premises of the subproof
      have hGw : ∀ g ∈ rupNegate C :: dbList st0.db, g.sat w :=
        List.forall_mem_cons.mpr ⟨hnC, (forall_dbList_iff _ w).mpr hw⟩
      -- freshness, checked when a scope is used or the order is touched
      have hFR : (hasScope items || !untouchedOrder z subst) = true →
          (∀ x, Sat.PB.Dominance.ImgFree subst O.aux x) ∧
          (∀ g ∈ rupNegate C :: dbList st0.db, ∀ x ∈ Sat.PB.Dominance.varsOf g,
            x ∉ O.aux) ∧
          (∀ c ∈ dbList freshDb, ∀ x ∈ Sat.PB.Dominance.varsOf c, x ∉ O.aux) ∧
          (∀ x ∈ Sat.PB.Dominance.varsOf (PBCatcher.normalizeConstr C), x ∉ O.aux) ∧
          termsAuxFree O.aux st0.curObj = true := by
        intro hu
        have hf : domFresh O.aux freshDb (PBCatcher.normalizeConstr C) st0.curObj subst =
            true := by
          cases hd : domFresh O.aux freshDb (PBCatcher.normalizeConstr C) st0.curObj subst
          · exfalso; apply hfr; rw [hu, hd]; rfl
          · rfl
        simp only [domFresh, Bool.and_eq_true] at hf
        obtain ⟨⟨⟨hF1, hF2⟩, hF3⟩, hF4⟩ := hf
        refine ⟨imgFree_of_substAuxFree hF4, ?_, dbList_auxFree hF1,
          varsOf_free_of_termsAuxFree hF2, hF3⟩
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact rupNegate_auxFree hF2
        · exact dbList_auxFree hF1 g (hdbF g hg)
      -- proved goals of compatible provenance hold at every model of the
      -- premises (and of `Spec[σ≤]` when a scope is used)
      have hleq : ∀ ρ', (∀ g ∈ rupNegate C :: dbList st0.db, g.sat ρ') →
          (hasScope items = true → ∀ s ∈ O.spec, (Sat.PB.applySubstConstr
            (Sat.PB.Dominance.sigmaLeq O z subst) s).sat ρ') →
          ∀ p ∈ proved, provLeqOk p.2.2 = true → p.2.1.sat ρ' := by
        intro ρ' hG hS p hpm hpk
        obtain ⟨hnC', hdb'⟩ := List.forall_mem_cons.mp hG
        apply (hok ρ' ((forall_dbList_iff _ ρ').mp hdb') hnC').1 p hpm
        cases hsc : hasScope items
        · rw [hsc] at hsp
          simp only [Bool.false_eq_true, ↓reduceIte] at hsp
          subst hsp
          exact ScopeCtx_none
        · rw [hsc] at hsp
          simp only [↓reduceIte] at hsp
          subst hsp
          apply provLeqOk_ctx hpk
          intro prem hprem c hc
          simp only [redScopePrem, Option.some.injEq] at hprem
          subst hprem
          exact substGoal_map_sat (hS hsc) c hc
      -- an aux-free goal list proved under the premises holds at `w`
      have helim : ∀ H : List Constr,
          (hasScope items = true → ∀ hc ∈ H, ∀ x ∈ Sat.PB.Dominance.varsOf hc, x ∉ O.aux) →
          (∀ ρ', (∀ g ∈ rupNegate C :: dbList st0.db, g.sat ρ') →
            (hasScope items = true → ∀ s ∈ O.spec, (Sat.PB.applySubstConstr
              (Sat.PB.Dominance.sigmaLeq O z subst) s).sat ρ') → ∀ hc ∈ H, hc.sat ρ') →
          ∀ hc ∈ H, hc.sat w := by
        intro H hHaux hH
        cases hsc : hasScope items
        · exact hH w hGw (fun hf => by rw [hsc] at hf; cases hf)
        · obtain ⟨himg', hGaux, -, -, -⟩ := hFR (by simp [hsc])
          exact Sat.PB.Dominance.specElim_leq (H := H) hgood.wf hgood.vars hgood.isSpec hz
            hzaux (fun l _ => himg' l.var) hGaux (hHaux hsc)
            (fun ρ' hG hS => hH ρ' hG (fun _ => hS)) w hGw
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- `#1`: `C|ω`
        have hel := helim [Sat.PB.applySubstConstr subst (PBCatcher.normalizeConstr C)]
          (fun hsc hc hmem => by
            rw [List.mem_singleton] at hmem
            subst hmem
            obtain ⟨himg', -, -, hCaux, -⟩ := hFR (by simp [hsc])
            exact Sat.PB.Dominance.varsOf_applySubstConstr_free hCaux (fun x _ => himg' x))
          (fun ρ' hG hS hc hmem => by
            rw [List.mem_singleton] at hmem
            subst hmem
            have hg1 := domHashCovered_sound _ proved _ _ ρ' h1 (List.forall_mem_cons.mp hG).1
              (hleq ρ' hG hS)
            exact Sat.PB.applySubstConstr_sound subst _ ρ'
              (normalize_sat C _ (substGoal_sat subst C ρ' hg1)))
          _ (List.mem_singleton_self _)
        exact normalize_sat_rev C _ (Sat.PB.applySubstConstr_sat_rev subst _ w hel)
      · -- the database goals
        have hel := helim ((dbList goalDb).map (Sat.PB.applySubstConstr subst))
          (fun hsc hc hmem => by
            obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hmem
            obtain ⟨himg', -, hFaux, -, -⟩ := hFR (by simp [hsc])
            exact Sat.PB.Dominance.varsOf_applySubstConstr_free (hFaux D (hgF D hD))
              (fun x _ => himg' x))
          (fun ρ' hG hS hc hmem => by
            obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hmem
            obtain ⟨hnC', hdb'⟩ := List.forall_mem_cons.mp hG
            have hdbρ := (forall_dbList_iff _ ρ').mp hdb'
            obtain ⟨⟨id, D'⟩, hmemt, rfl⟩ := List.mem_map.mp hD
            have hcov := List.all_eq_true.mp hdbg (id, D') hmemt
            have hget : goalDb.get? id = some D' := by
              rw [Std.HashMap.get?_eq_getElem?]
              exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmemt
            exact Sat.PB.applySubstConstr_sound subst _ ρ'
              (dbGoalCovered_sound subst _ lookupDb (leqProved proved) D' ρ' hcov
                (hlook ρ' hdbρ) (hgoal ρ' hdbρ id D' hget) hnC'
                (leqProved_sat (hleq ρ' hG hS))))
        intro id D hget
        exact Sat.PB.applySubstConstr_sat_rev subst D w
          (hel _ (List.mem_map.mpr ⟨D, mem_dbList_of_get? hget, rfl⟩))
      · -- the objective goal
        unfold domObjCovered at hobj
        simp only [Bool.or_eq_true, Bool.not_eq_true'] at hobj
        rcases hobj with hna | hcov
        · simp only [objVal]
          rw [Sat.PB.evalSum_applyValuation_noSubst subst w _ hna]
          exact Nat.le_refl _
        · have hel := helim [objGoalRaw subst st0.curObj]
            (fun hsc hc hmem => by
              rw [List.mem_singleton] at hmem
              subst hmem
              obtain ⟨himg', -, -, -, hF3⟩ := hFR (by simp [hsc])
              exact objGoalRaw_auxFree hF3 himg')
            (fun ρ' hG hS hc hmem => by
              rw [List.mem_singleton] at hmem
              subst hmem
              have := domHashCovered_sound _ proved _ _ ρ' hcov
                (List.forall_mem_cons.mp hG).1 (hleq ρ' hG hS)
              rw [objGoalConstr_eq] at this
              exact normalize_sat_rev _ ρ' this)
            _ (List.mem_singleton_self _)
          exact objGoalConstr_sound subst st0.curObj w
            (by rw [objGoalConstr_eq]; exact normalize_sat _ w hel)
      · -- the order: `w∘ω ⪯ w`
        by_cases hu : untouchedOrder z subst = true
        · apply Sat.PB.Dominance.leq_of_untouched hgood.refl hz
          intro l hl
          have := List.all_eq_true.mp hu l hl
          simpa using this
        · have hordc : domOrderGoalsCovered (rupNegate C) proved 2
              (O.defs.map (substGoal (Sat.PB.Dominance.sigmaLeq O z subst))) = true := by
            simp only [Bool.or_eq_true] at hord
            exact hord.resolve_left hu
          obtain ⟨himg', hGaux, -, -, -⟩ := hFR (by simp [hu])
          exact Sat.PB.Dominance.ordLeq_of_goal (G := rupNegate C :: dbList st0.db)
            hgood.wf hgood.vars hgood.isSpec hz hzaux (fun l _ => himg' l.var) hGaux
            (fun ρ' hG hS d hd => by
              have := domOrderGoalsCovered_sound (rupNegate C) proved ρ'
                (List.forall_mem_cons.mp hG).1 (hleq ρ' hG (fun _ => hS)) 2 _ hordc
              exact normalize_sat_rev _ ρ' (this _ (List.mem_map.mpr ⟨d, hd, rfl⟩)))
            w hGw
    · cases h

theorem checkRedOrder_nextId_le
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId)
    (st0 : BoolCheckState) (O : Sat.PB.Dominance.OrderData) (z : List Sat.PB.Literal)
    (goalDb lookupDb freshDb : Std.HashMap Nat Constr)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (qedHint : Option Nat) (fid : Nat)
    (h : checkRedOrder execFn st0 O z goalDb lookupDb freshDb subst C items qedHint =
      some fid) :
    st0.nextId ≤ fid := by
  unfold checkRedOrder at h
  split at h
  · cases h
  dsimp only at h
  generalize (if hasScope items = true then redScopePrem O z subst
    else fun _ => none) = sp at h
  cases hp : processScopedItems execFn
      (redOrdGoalOf O z subst C st0.curObj (fun n => lookupDb[n]?)) (fun _ => false) []
      sp { st0 with db := st0.db.insert st0.nextId (rupNegate C), nextId := st0.nextId + 1 }
      items [] [] with
  | none => rw [hp] at h; cases h
  | some r =>
    obtain ⟨fin, proved, contras⟩ := r
    rw [hp] at h
    dsimp only at h
    have h1 := processScopedItems_nextId_le execFn _ _ _ _ hmono items _ [] [] fin proved
      contras hp
    simp only [] at h1
    have key : ∀ b : Bool, (if b = true then some fin.nextId else none) =
        some fid → st0.nextId ≤ fid := by
      intro b hb
      cases b
      · simp at hb
      · simp only [ite_true, Option.some.injEq] at hb; omega
    exact key _ h

/-- Soundness of `checkRedAny` (with or without a loaded order): the facts of
`checkRedundance_sound`, and `w∘ω ⪯ w` for the loaded order. -/
theorem checkRedAny_sound
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (st0 : BoolCheckState) (ord : Option (Sat.PB.Dominance.OrderData × List Sat.PB.Literal))
    (goalDb lookupDb freshDb : Std.HashMap Nat Constr)
    (hgoal : ∀ v, DBSatBy st0.db v → DBSatBy goalDb v)
    (hlook : ∀ v, DBSatBy st0.db v → DBSatBy lookupDb v)
    (hdbF : ∀ c ∈ dbList st0.db, c ∈ dbList freshDb)
    (hgF : ∀ c ∈ dbList goalDb, c ∈ dbList freshDb)
    (hord : ∀ O z, ord = some (O, z) → Sat.PB.Dominance.GoodOrder O ∧
      z.length = O.left.length ∧ ∀ l ∈ z, l.var ∉ O.aux)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (qedHint : Option Nat) (fid : Nat)
    (h : checkRedAny execFn st0 ord goalDb lookupDb freshDb subst C items qedHint =
      some fid)
    (w : Valuation) (hw : DBSatBy st0.db w) (hC : ¬ C.sat w) :
    C.sat (Sat.PB.applyValuation subst w) ∧
      DBSatBy goalDb (Sat.PB.applyValuation subst w) ∧
      objVal st0.curObj (Sat.PB.applyValuation subst w) ≤ objVal st0.curObj w ∧
      ∀ O z, ord = some (O, z) →
        Sat.PB.Dominance.Leq O z (Sat.PB.applyValuation subst w) w := by
  cases ord with
  | none =>
    simp only [checkRedAny] at h
    obtain ⟨g1, g2, g3⟩ := checkRedundance_sound execFn hexec st0 goalDb lookupDb hgoal
      hlook subst C items qedHint fid h w hw hC
    exact ⟨g1, g2, g3, fun _ _ hoz => by cases hoz⟩
  | some oz =>
    obtain ⟨O, z⟩ := oz
    simp only [checkRedAny] at h
    obtain ⟨hg, hz, hza⟩ := hord O z rfl
    obtain ⟨g1, g2, g3, g4⟩ := checkRedOrder_sound execFn hexec st0 O z goalDb lookupDb
      freshDb hgoal hlook hdbF hgF subst C items qedHint fid h hg hz hza w hw hC
    refine ⟨g1, g2, g3, fun O' z' hoz => ?_⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at hoz
    obtain ⟨rfl, rfl⟩ := hoz
    exact g4

theorem checkRedAny_qed_implied
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (st0 : BoolCheckState) (ord : Option (Sat.PB.Dominance.OrderData × List Sat.PB.Literal))
    (goalDb lookupDb freshDb : Std.HashMap Nat Constr)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (cid fid : Nat)
    (h : checkRedAny execFn st0 ord goalDb lookupDb freshDb subst C items (some cid) =
      some fid) :
    ∀ w, DBSatBy st0.db w → C.sat w := by
  cases ord with
  | none =>
    simp only [checkRedAny] at h
    exact checkRedundance_qed_implied execFn hexec st0 goalDb lookupDb subst C items cid
      fid h
  | some oz =>
    obtain ⟨O, z⟩ := oz
    simp only [checkRedAny] at h
    exact checkRedOrder_qed_implied execFn hexec st0 O z goalDb lookupDb freshDb subst C
      items cid fid h

theorem checkRedAny_nextId_le
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId)
    (st0 : BoolCheckState) (ord : Option (Sat.PB.Dominance.OrderData × List Sat.PB.Literal))
    (goalDb lookupDb freshDb : Std.HashMap Nat Constr)
    (subst : List (Nat × Sat.PB.SubstVal)) (C : Constr)
    (items : List PBCatcher.ProofStep) (qedHint : Option Nat) (fid : Nat)
    (h : checkRedAny execFn st0 ord goalDb lookupDb freshDb subst C items qedHint =
      some fid) :
    st0.nextId ≤ fid := by
  cases ord with
  | none =>
    simp only [checkRedAny] at h
    exact checkRedundance_nextId_le execFn hmono st0 goalDb lookupDb subst C items qedHint
      fid h
  | some oz =>
    obtain ⟨O, z⟩ := oz
    simp only [checkRedAny] at h
    exact checkRedOrder_nextId_le execFn hmono st0 O z goalDb lookupDb freshDb subst C
      items qedHint fid h

/-- `CoreValidDB` carries over to a new database whose core models are models
of the old core, when every model of the old database has a model of the new
one that is below it in the order and not worse (design T4: the `red` step;
`Sat.PB.Dominance.coreValid_red`). -/
theorem coreValidDB_transport {O : Sat.PB.Dominance.OrderData}
    {z : List Sat.PB.Literal} {db db' : Std.HashMap Nat Constr}
    {core core' : Std.HashSet Nat} {f : Valuation → Int}
    (htrans : ∀ p q r, O.Rel p q → O.Rel q r → O.Rel p r)
    (hcore : ∀ ρ, CoreSatBy db' core' ρ → CoreSatBy db core ρ)
    (htr : ∀ w, DBSatBy db w → ∃ w', DBSatBy db' w' ∧ f w' ≤ f w ∧
      Sat.PB.Dominance.Leq O z w' w)
    (h : CoreValidDB O z db core f) : CoreValidDB O z db' core' f := by
  intro ρ hρ
  obtain ⟨ρ1, h1, h2, h3⟩ := h ρ (hcore ρ hρ)
  obtain ⟨ρ2, h4, h5, h6⟩ := htr ρ1 h1
  exact ⟨ρ2, h4, Sat.PB.Dominance.leq_trans htrans h6 h2, Int.le_trans h5 h3⟩

/-- A model of the core without the erased id `did` that satisfies the erased
constraint is a model of the old core. -/
theorem CoreSatBy_of_erase {db : Std.HashMap Nat Constr} {core : Std.HashSet Nat}
    {did : Nat} {D : Constr} {ρ : Valuation} (hD : db[did]? = some D) (hDs : D.sat ρ)
    (hρ : CoreSatBy (db.erase did) (core.erase did) ρ) : CoreSatBy db core ρ := by
  intro id c hid hget
  by_cases heq : did = id
  · subst heq
    rw [Std.HashMap.get?_eq_getElem?, hD] at hget
    cases hget
    exact hDs
  · have hne : (did == id) = false := by
      cases hb : did == id
      · rfl
      · exact absurd (beq_iff_eq.mp hb) heq
    apply hρ id c
    · rw [Std.HashSet.contains_erase, hne, hid]; rfl
    · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_erase, hne]
      rw [Std.HashMap.get?_eq_getElem?] at hget
      simpa using hget

/-- `red` step: the objective fields are unchanged, and every valuation of
the old database has a counterpart in the new one that is at least as good
under the current objective and below it in the loaded order. Under
`strengthening_to_core` the database goals range over the core only; the
hypothesis `hci` (the invariant clause `CoreImplied`) lifts the counterpart
from the core to the whole database. `hoi` supplies the order facts of the
redundance check (and reflexivity for the identity counterpart). -/
theorem redStep_sound
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (state : BoolCheckState) (constr : PBCatcher.OPBConstr)
    (substPairs : List (String × String)) (items : List PBCatcher.ProofStep)
    (qedHint : Option Nat) (st' : BoolCheckState)
    (hci : state.s2c = true → ∀ ρ, CoreSatBy state.db state.coreIds ρ →
      DBSatBy state.db ρ)
    (hoi : OrdInv state)
    (h : redStep execFn state constr substPairs items qedHint = some st') :
    SameObjFields st' state ∧
      ∀ w, DBSatBy state.db w → ∃ w', DBSatBy st'.db w' ∧
        opbVal st'.curObj st'.curOffset w' ≤ opbVal state.curObj state.curOffset w ∧
        ∀ O z, state.ord = some (O, z) → Sat.PB.Dominance.Leq O z w' w := by
  unfold redStep at h
  split at h
  · cases h
  · rename_i C _
    split at h
    · cases h
    · rename_i subst _
      dsimp only at h
      generalize hg : (if state.s2c = true then
        state.db.filter (fun id _ => state.coreIds.contains id)
        else state.db) = goalDb at h
      split at h
      · cases h
      · rename_i fid hchk
        cases h
        refine ⟨⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, fun w hw => ?_⟩
        by_cases hC : C.sat w
        · refine ⟨w, DBSatBy_insert _ _ _ w hw (normalize_sat C w hC), Int.le_refl _,
            fun O z hoz => ?_⟩
          obtain ⟨hgo, hz, -, -⟩ := hoi O z hoz
          exact Sat.PB.Dominance.leq_refl hgo.refl hz w
        · have hgoal : ∀ v, DBSatBy state.db v → DBSatBy goalDb v := by
            intro v hv
            rw [← hg]
            split
            · exact DBSatBy_filter _ _ v hv
            · exact hv
          have hgF : ∀ c ∈ dbList goalDb, c ∈ dbList state.db := by
            intro c hc
            rw [← hg] at hc
            split at hc
            · exact mem_dbList_filter hc
            · exact hc
          obtain ⟨h1, h2, h3, h4⟩ := checkRedAny_sound execFn hexec state state.ord
            goalDb state.db state.db hgoal (fun _ hv => hv) (fun _ hc => hc) hgF
            (fun O z hoz => let ⟨a, b, c, _⟩ := hoi O z hoz; ⟨a, b, c⟩)
            subst C items qedHint fid hchk w hw hC
          have h2' : DBSatBy state.db (Sat.PB.applyValuation subst w) := by
            cases hs : state.s2c
            · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hg
              rw [hg]; exact h2
            · simp only [hs, ↓reduceIte] at hg
              rw [← hg] at h2
              exact hci hs _ ((DBSatBy_filter_core_iff _ _ _).mp h2)
          exact ⟨_, DBSatBy_insert _ _ _ _ h2' (normalize_sat C _ h1), by
            simp only [opbVal]; omega, h4⟩

/-- Shape of a `red` step: `C` (normalized) is inserted at an id `fid` at or
above the old counter, the counter moves past it, `fid` joins the core iff
`strengthening_to_core` is on, and the mode is unchanged. -/
theorem redStep_shape
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId)
    (state : BoolCheckState) (constr : PBCatcher.OPBConstr)
    (substPairs : List (String × String)) (items : List PBCatcher.ProofStep)
    (qedHint : Option Nat) (st' : BoolCheckState)
    (h : redStep execFn state constr substPairs items qedHint = some st') :
    ∃ fid C', state.nextId ≤ fid ∧ st'.db = state.db.insert fid C' ∧
      st'.nextId = fid + 1 ∧
      st'.coreIds = (if state.s2c then state.coreIds.insert fid
        else state.coreIds) ∧
      st'.s2c = state.s2c ∧ st'.ord = state.ord ∧ st'.orders = state.orders := by
  unfold redStep at h
  split at h
  · cases h
  · split at h
    · cases h
    · dsimp only at h
      generalize (if state.s2c = true then
        state.db.filter (fun id _ => state.coreIds.contains id)
        else state.db) = goalDb at h
      split at h
      · cases h
      · rename_i fid hchk
        cases h
        exact ⟨fid, _, checkRedAny_nextId_le execFn hmono _ _ _ _ _ _ _ _ _ fid
          hchk, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Checked deletion erases one core id `did` from the database and the
core, changes no other field the invariant depends on, and never decreases
the id counter. Under `strengthening_to_core` its check closes with
`qed : cid`, so the surviving core implies the erased constraint: a model of
the new core is a model of the old one. While an order is loaded the
check keeps `CoreValid` (design T5): a model of the new core falsifying the
erased constraint is mapped by the witness to a model of the old core below
it, whose database counterpart is below it again. -/
theorem delcCheckedStep_spec
    (execFn : BoolCheckState → List PBCatcher.ProofStep → Option BoolCheckState)
    (hexec : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → ∀ v, DBSatBy st.db v → DBSatBy st'.db v)
    (hmono : ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
      execFn st steps = some st' → st.nextId ≤ st'.nextId)
    (state : BoolCheckState) (ids : List Nat)
    (substPairs : List (String × String))
    (sub : Option (Array PBCatcher.ProofStep × Option Nat)) (st' : BoolCheckState)
    (h : delcCheckedStep execFn state ids substPairs sub = some st') :
    SameObjFields st' state ∧ ∃ did, st'.db = state.db.erase did ∧
      st'.coreIds = state.coreIds.erase did ∧ st'.s2c = state.s2c ∧
      state.nextId ≤ st'.nextId ∧ st'.ord = state.ord ∧ st'.orders = state.orders ∧
      (state.s2c = true → ∀ ρ, CoreSatBy st'.db st'.coreIds ρ →
        CoreSatBy state.db state.coreIds ρ) ∧
      (OrdInv state → OrdInv st') := by
  unfold delcCheckedStep at h
  dsimp only at h
  split at h
  · rename_i did items qedHint
    split at h
    · cases h
    · rename_i subst _
      split at h
      · cases h
      · rename_i hq
        split at h
        · cases h
        · split at h
          · cases h
          · rename_i D hD
            split at h
            · cases h
            · rename_i fid hchk
              cases h
              have hle := checkRedAny_nextId_le execFn hmono _ _ _ _ _ _ _ _ _
                fid hchk
              have hsubF : ∀ c ∈ dbList ((state.db.erase did).filter
                  fun id _ => (state.coreIds.erase did).contains id),
                  c ∈ dbList (state.db.erase did) := fun c hc => mem_dbList_filter hc
              refine ⟨⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, did, rfl, rfl, rfl,
                hle, rfl, rfl, ?_, ?_⟩
              · intro hs ρ hρ
                cases qedHint with
                | none => simp [hs] at hq
                | some cid =>
                  have hDs : D.sat ρ := checkRedAny_qed_implied execFn hexec
                    _ _ _ _ _ subst D items.toList cid fid hchk ρ
                    ((DBSatBy_filter_core_iff _ _ _).mpr hρ)
                  exact CoreSatBy_of_erase hD hDs hρ
              · intro hoi O z hoz
                have hoz' : state.ord = some (O, z) := hoz
                obtain ⟨hgo, hz, hza, hcv⟩ := hoi O z hoz'
                refine ⟨hgo, hz, hza, coreValid_iff_DB.mpr ?_⟩
                have hcv' := coreValid_iff_DB.mp hcv
                intro ρ hρ
                by_cases hDs : D.sat ρ
                · obtain ⟨ρ', h1, h2, h3⟩ := hcv' ρ (CoreSatBy_of_erase hD hDs hρ)
                  exact ⟨ρ', DBSatBy_erase_fold state.db [did] ρ' h1, h2, h3⟩
                · obtain ⟨g1, g2, g3, g4⟩ := checkRedAny_sound execFn hexec _ state.ord
                    _ _ (state.db.erase did) (fun _ hv => hv) (fun _ hv => hv) hsubF hsubF
                    (fun O z hoz => let ⟨a, b, c, _⟩ := hoi O z hoz; ⟨a, b, c⟩)
                    subst D items.toList qedHint fid hchk ρ
                    ((DBSatBy_filter_core_iff _ _ _).mpr hρ) hDs
                  obtain ⟨ρ', h1, h2, h3⟩ := hcv' _ (CoreSatBy_of_erase hD g1
                    ((DBSatBy_filter_core_iff _ _ _).mp g2))
                  refine ⟨ρ', DBSatBy_erase_fold state.db [did] ρ' h1,
                    Sat.PB.Dominance.leq_trans hgo.trans h2 (g4 O z hoz'), ?_⟩
                  simp only [opbVal] at h3 ⊢
                  have g3' : objVal state.curObj (Sat.PB.applyValuation subst ρ) ≤
                      objVal state.curObj ρ := g3
                  omega
  · cases h

theorem StateInv_init (F : Array Constr) (numVars : Nat) (obj : Objective)
    (offset : Int := 0) :
    StateInv (BoolCheckState.fromConstrs F numVars obj offset) :=
  ⟨fun v hF _ => ⟨v, fun id c hget => by
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp
        (mkDBRec_mem (F.toList.map PBCatcher.normalizeConstr) 1 id c hget)
      exact normalize_sat c0 v (hF c0 hc0),
    Int.le_refl _⟩,
   fun b hb => by simp [BoolCheckState.fromConstrs] at hb,
   fun hs => by simp [BoolCheckState.fromConstrs] at hs,
   fun id c hget => by
     have := mkDBRec_lt (F.toList.map PBCatcher.normalizeConstr) 1 id c hget
     simp only [List.length_map, Array.length_toList] at this
     show id < F.size + 1
     omega,
   fun p hp => by simp [BoolCheckState.fromConstrs] at hp,
   fun O z h => by simp [BoolCheckState.fromConstrs] at h⟩

/-- Main step lemma with field preservation: execution preserves the
optimization invariant and never changes the formula or the original
objective. -/
theorem execStepsFuel_inv_preserve_fields : ∀ (fuel : Nat)
    (state state' : BoolCheckState) (steps : List PBCatcher.ProofStep),
    StateInv state →
    execStepsFuel fuel state steps = some state' →
    StateInv state' ∧ state'.origConstrs = state.origConstrs ∧
      state'.objective = state.objective ∧ state'.offset = state.offset := by
  intro fuel state state' steps hinv hsteps
  induction steps generalizing state with
  | nil =>
    unfold execStepsFuel at hsteps
    injection hsteps with h; subst h; exact ⟨hinv, rfl, rfl, rfl⟩
  | cons step rest ih_rest =>
    unfold execStepsFuel at hsteps
    simp only [] at hsteps
    have hci : CoreImplied state := hinv.2.2.1
    have hib : IdsBelowDb state.db state.nextId := hinv.2.2.2.1
    have hsg : StoredGood state := hinv.2.2.2.2.1
    have hoi : OrdInv state := hinv.2.2.2.2.2
    -- the step lemmas' hypotheses on the subproof executor
    have hexecN : ∀ n, ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
        execStepsFuel n st steps = some st' → ∀ v, DBSatBy st.db v →
          DBSatBy st'.db v :=
      fun n st st' steps hls hex v hv =>
        execStepsFuel_implied n st st' steps hls hex v hv
    have hmonoN : ∀ n, ∀ st st' steps, (∀ s ∈ steps, isLStep s = true) →
        execStepsFuel n st steps = some st' → st.nextId ≤ st'.nextId :=
      fun n st st' steps hls hex => execStepsFuel_nextId_le n st st' steps hls hex
    -- an implied constraint inserted at the counter, into the derived set
    have himplied : ∀ (c : Constr), (∀ v, DBSatBy state.db v → c.sat v) →
        execStepsFuel fuel { state with
          db := state.db.insert state.nextId c
          nextId := state.nextId + 1 } rest = some state' →
        StateInv state' ∧ state'.origConstrs = state.origConstrs ∧
          state'.objective = state.objective ∧
          state'.offset = state.offset := by
      intro c himpl hrest
      apply ih_rest _ _ hrest
      exact ⟨DBOpt_insert_dbImplied state.nextId _ hinv.1 himpl,
        hinv.2.1,
        fun hs => coreImplied_insert_implied
          (IdsBelowDb_fresh hib (Nat.le_refl _)) himpl (hci hs),
        IdsBelowDb_insert hib (Nat.lt_succ_self _) (Nat.le_succ _), hsg,
        OrdInv_of hoi rfl rfl rfl (fun _ _ _ hcv => coreValidDB_insert_implied
          (IdsBelowDb_fresh hib (Nat.le_refl _)) himpl hcv)⟩
    -- a step that keeps the objective fields and maps every valuation of
    -- the database to an at least as good one (current objective)
    have hstep : ∀ st : BoolCheckState, KeepsObj st state →
        (∀ w, DBSatBy state.db w → ∃ w', DBSatBy st.db w' ∧
          opbVal st.curObj st.curOffset w' ≤
            opbVal state.curObj state.curOffset w) →
        CoreImplied st → IdsBelowDb st.db st.nextId → StoredGood st → OrdInv st →
        execStepsFuel fuel st rest = some state' →
        StateInv state' ∧ state'.origConstrs = state.origConstrs ∧
          state'.objective = state.objective ∧
          state'.offset = state.offset := by
      intro st hkeep hdb hci' hib' hsg' hoi' hrest
      obtain ⟨hF, hO, hOff, hB, hBW⟩ := hkeep
      have hinv' : StateInv st := by
        refine ⟨fun v hFv himp => ?_, ?_, hci', hib', hsg', hoi'⟩
        · rw [hF] at hFv
          rw [hO, hOff, hB] at himp
          obtain ⟨w, hw, hle⟩ := hinv.1 v hFv himp
          obtain ⟨w', hw', hle'⟩ := hdb w hw
          rw [hO, hOff]
          exact ⟨w', hw', Int.le_trans hle' hle⟩
        · rw [hF, hO, hOff, hBW]; exact hinv.2.1
      obtain ⟨h1, h2, h3, h4⟩ := ih_rest st hinv' hrest
      exact ⟨h1, h2.trans hF, h3.trans hO, h4.trans hOff⟩
    -- a `dom` step (both constructors)
    have hdom : ∀ n constr substPairs items qedHint st,
        domStep (execStepsFuel n) state constr substPairs items qedHint = some st →
        execStepsFuel fuel st rest = some state' →
        StateInv state' ∧ state'.origConstrs = state.origConstrs ∧
          state'.objective = state.objective ∧ state'.offset = state.offset := by
      intro n constr substPairs items qedHint st hr hrest
      obtain ⟨hsame, ⟨fid, C', hfid, hdb', hnext, hcore, hs2c, _, hords⟩, hdb, hoi'⟩ :=
        domStep_spec (execStepsFuel n) (hexecN n) (hmonoN n) state constr substPairs
          items qedHint st hib hoi hr
      refine hstep st hsame.toKeepsObj hdb ?_ ?_ (StoredGood_of hords hsg) hoi' hrest
      · intro hs
        have hs0 : state.s2c = true := hs2c ▸ hs
        rw [hdb', hcore]
        simp only [hs0, ↓reduceIte]
        exact coreImplied_insert_core (IdsBelowDb_fresh hib hfid) (hci hs0)
      · rw [hdb', hnext]
        exact IdsBelowDb_insert hib (Nat.lt_succ_self _) (by omega)
    -- a `red` step (both constructors)
    have hred : ∀ n constr substPairs items qedHint st,
        redStep (execStepsFuel n) state constr substPairs items qedHint = some st →
        execStepsFuel fuel st rest = some state' →
        StateInv state' ∧ state'.origConstrs = state.origConstrs ∧
          state'.objective = state.objective ∧ state'.offset = state.offset := by
      intro n constr substPairs items qedHint st hr hrest
      obtain ⟨hsame, htr⟩ := redStep_sound (execStepsFuel n) (hexecN n)
        state constr substPairs items qedHint st hci hoi hr
      obtain ⟨fid, C', hfid, hdb', hnext, hcore, hs2c, hordst, hords⟩ :=
        redStep_shape (execStepsFuel n) (hmonoN n) state constr substPairs items
          qedHint st hr
      refine hstep st hsame.toKeepsObj (fun w hw => by
          obtain ⟨w', h1, h2, -⟩ := htr w hw
          exact ⟨w', h1, h2⟩) ?_ ?_ (StoredGood_of hords hsg) ?_ hrest
      · intro hs
        have hs0 : state.s2c = true := hs2c ▸ hs
        rw [hdb', hcore]
        simp only [hs0, ↓reduceIte]
        exact coreImplied_insert_core (IdsBelowDb_fresh hib hfid) (hci hs0)
      · rw [hdb', hnext]
        exact IdsBelowDb_insert hib (Nat.lt_succ_self _) (by omega)
      · -- `CoreValid` with the new constraint (design T4)
        apply OrdInv_of hoi hordst hsame.curObj hsame.curOffset
        intro O z hoz hcv
        refine coreValidDB_transport (hoi O z hoz).1.trans ?_ ?_ hcv
        · intro ρ hρ
          rw [hdb', hcore] at hρ
          apply CoreSatBy_of_insert_fresh (IdsBelowDb_fresh hib hfid) _ hρ
          intro id hid
          split
          · rw [Std.HashSet.contains_insert, hid, Bool.or_true]
          · exact hid
        · intro w hw
          obtain ⟨w', h1, h2, h3⟩ := htr w hw
          refine ⟨w', h1, ?_, h3 O z hoz⟩
          rw [hsame.curObj, hsame.curOffset] at h2
          exact h2
    cases step with
    | formulaSize n =>
      by_cases hfs : state.formulaSize != n
      · simp [hfs] at hsteps
      · simp [hfs] at hsteps; exact ih_rest state hinv hsteps
    | pol ops =>
      match hpol : execPolRPNBool ops state.db with
      | some result =>
        simp [hpol] at hsteps
        refine himplied _ ?_ hsteps
        intro v hdb
        exact normalize_sat result v
          (execPolRPNBool_implied ops state.db ⟨state.db.toList.map Prod.snd⟩
            result (DBSound_of_toList state.db) hpol v
            (toList_sat_of_DBSat state.db v hdb))
      | none => simp [hpol] at hsteps
    | rup constr hints =>
      match hparse : PBCatcher.opbConstrToPB constr with
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
          refine himplied _ ?_ hsteps
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
          cases hparse : PBCatcher.opbConstrToPB constr with
          | error _ => simp [hparse] at hsteps
          | ok T0 =>
            simp only [hparse] at hsteps
            by_cases himp : impliesSyntactic (PBCatcher.normalizeConstr S)
                (PBCatcher.normalizeConstr T0) = true
            · rw [if_pos himp] at hsteps
              refine himplied _ ?_ hsteps
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
          match hparse : PBCatcher.opbConstrToPB constr with
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
                      db := state.db.insert state.nextId
                        (PBCatcher.normalizeConstr pbConstr.negate)
                      nextId := state.nextId + 1 }
                    innerSteps.toList with
              | some finalSub =>
                simp [hinner] at hsteps
                have hle := execStepsFuel_nextId_le n _ finalSub
                  innerSteps.toList (lsteps_of_not_any innerSteps hany) hinner
                dsimp only at hle
                match hres : finalSub.db[resultId]? with
                | some c =>
                  simp [hres] at hsteps
                  by_cases hcontra : c.isContra
                  · simp [hcontra] at hsteps
                    have himpl : ∀ v, DBSatBy state.db v →
                        (PBCatcher.normalizeConstr pbConstr).sat v := by
                      intro v hdb
                      apply normalize_sat
                      apply sat_of_not_negate_sat pbConstr v hcs'
                      intro hneg_sat
                      have hfin := execStepsFuel_implied n _ finalSub
                        innerSteps.toList (lsteps_of_not_any innerSteps hany)
                        hinner v (DBSatBy_insert _ _ _ v hdb
                          (normalize_sat _ v hneg_sat))
                      exact contra_unsat c v (by
                        simp [Constr.isContra] at hcontra; exact hcontra)
                        (hfin resultId c (by rwa [Std.HashMap.get?_eq_getElem?]))
                    apply ih_rest _ _ hsteps
                    exact ⟨DBOpt_insert_dbImplied finalSub.nextId _ hinv.1 himpl,
                      hinv.2.1,
                      fun hs => coreImplied_insert_implied
                        (IdsBelowDb_fresh hib (by omega)) himpl (hci hs),
                      IdsBelowDb_insert hib (Nat.lt_succ_self _)
                        (by dsimp only; omega), hsg,
                      OrdInv_of hoi rfl rfl rfl (fun _ _ _ hcv =>
                        coreValidDB_insert_implied (IdsBelowDb_fresh hib (by omega))
                          himpl hcv)⟩
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
          exact hred n _ _ _ _ st hr hsteps
    | dom constr substPairs goals =>
      match fuel with
      | 0 => simp at hsteps
      | n + 1 =>
        simp only [] at hsteps
        cases hr : domStep (execStepsFuel n) state constr substPairs
            (goalsToItems goals) none with
        | none => rw [hr] at hsteps; simp at hsteps
        | some st =>
          rw [hr] at hsteps
          exact hdom n _ _ _ _ st hr hsteps
    | strengthening rule constr substPairs items qedHint =>
      cases rule with
      | dom =>
        match fuel with
        | 0 => simp at hsteps
        | n + 1 =>
          simp only [] at hsteps
          cases hr : domStep (execStepsFuel n) state constr substPairs
              items.toList qedHint with
          | none => rw [hr] at hsteps; simp at hsteps
          | some st =>
            rw [hr] at hsteps
            exact hdom n _ _ _ _ st hr hsteps
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
            exact hred n _ _ _ _ st hr hsteps
    | delcChecked ids substPairs sub =>
      match fuel with
      | 0 => simp at hsteps
      | n + 1 =>
        simp only [] at hsteps
        cases hd : delcCheckedStep (execStepsFuel n) state ids substPairs sub with
        | none => rw [hd] at hsteps; simp at hsteps
        | some st =>
          rw [hd] at hsteps
          obtain ⟨hsame, did, hdb, -, hs2c, hnext, -, hords, hcs, hoi'⟩ :=
            delcCheckedStep_spec _ (hexecN n) (hmonoN n) state ids substPairs
              sub st hd
          refine hstep st hsame.toKeepsObj (fun w hw => ⟨w, by
            rw [hdb]
            exact DBSatBy_erase_fold state.db [did] w hw, by
            rw [hsame.curObj, hsame.curOffset]; exact Int.le_refl _⟩) ?_ ?_
            (StoredGood_of hords hsg) (hoi' hoi) hsteps
          · intro hs ρ hρ
            have hs0 : state.s2c = true := hs2c ▸ hs
            rw [hdb]
            exact DBSatBy_erase_fold state.db [did] ρ (hci hs0 ρ (hcs hs0 ρ hρ))
          · rw [hdb]
            exact IdsBelowDb_mono (IdsBelowDb_erase_fold [did] hib) hnext
    | deld ids =>
      cases hc : (ids.any state.coreIds.contains ||
          (state.coreOnly && ids.any state.db.contains)) with
      | true => simp [hc] at hsteps
      | false =>
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hsteps
        have hany : ids.any state.coreIds.contains = false := by
          simp only [Bool.or_eq_false_iff] at hc; exact hc.1
        apply ih_rest _ _ hsteps
        have hnc : ∀ id ∈ ids, state.coreIds.contains id = false := by
          intro id hm
          cases h : state.coreIds.contains id
          · rfl
          · have h1 := List.any_eq_true.mpr ⟨id, hm, h⟩
            rw [hany] at h1; cases h1
        refine ⟨DBOpt_erase_fold state.db ids hinv.1, hinv.2.1, ?_,
          IdsBelowDb_erase_fold ids hib, hsg,
          OrdInv_of hoi rfl rfl rfl (fun _ _ _ hcv =>
            coreValidDB_erase_derived ids hnc hcv)⟩
        intro hs ρ hρ
        refine DBSatBy_erase_fold state.db ids ρ (hci hs ρ ?_)
        intro id c hid hget
        have hnot : id ∉ ids := fun hm => by
          have h1 := List.any_eq_true.mpr ⟨id, hm, hid⟩
          rw [hany] at h1; cases h1
        exact hρ id c (HashSet_contains_erase_fold _ _ _ hid hnot)
          (by rw [HashMap_get?_erase_fold, if_neg hnot]; exact hget)
    | delc ids =>
      by_cases hc : ((state.ord.isSome || state.s2c) && !allCore state) = true
      · simp only [hc, if_true] at hsteps; simp at hsteps
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hsteps
        apply ih_rest _ _ hsteps
        have hall : (state.ord.isSome || state.s2c) = true → allCore state = true := by
          intro hos
          cases h : allCore state
          · exfalso; apply hc; rw [hos, h]; rfl
          · rfl
        -- with every constraint core, the core after the deletion is the
        -- whole database
        have hmod : allCore state = true → ∀ ρ,
            CoreSatBy (ids.foldl (fun db id => db.erase id) state.db)
              (ids.foldl (fun s id => s.erase id) state.coreIds) ρ →
            DBSatBy (ids.foldl (fun db id => db.erase id) state.db) ρ := by
          intro hal ρ hρ id c hget
          have hget0 := hget
          rw [HashMap_get?_erase_fold] at hget
          by_cases hm : id ∈ ids
          · simp [hm] at hget
          · simp only [hm, ↓reduceIte] at hget
            exact hρ id c (HashSet_contains_erase_fold _ _ _
              (allCore_contains hal hget) hm) hget0
        refine ⟨DBOpt_erase_fold state.db ids hinv.1, hinv.2.1,
          fun hs => hmod (hall (by rw [show state.s2c = true from hs, Bool.or_true])),
          IdsBelowDb_erase_fold ids hib, hsg, ?_⟩
        -- while an order is loaded: the identity counterpart (reflexivity)
        intro O z hoz
        have hoz' : state.ord = some (O, z) := hoz
        obtain ⟨hgo, hz, hza, -⟩ := hoi O z hoz'
        refine ⟨hgo, hz, hza, coreValid_iff_DB.mpr ?_⟩
        intro ρ hρ
        exact ⟨ρ, hmod (hall (by simp [hoz'])) ρ hρ,
          Sat.PB.Dominance.leq_refl hgo.refl hz ρ, Int.le_refl _⟩
    | core ids =>
      by_cases hc : ids.all state.db.contains = true
      · simp only [hc, if_true] at hsteps
        apply ih_rest _ _ hsteps
        exact ⟨hinv.1, hinv.2.1, fun hs ρ hρ => hci hs ρ (CoreSatBy_mono
          (fun id hid => HashSet_contains_insert_fold _ _ _ (Or.inl hid)) hρ),
          hib, hsg, OrdInv_of hoi rfl rfl rfl (fun _ _ _ hcv =>
            coreValidDB_mono_core (fun ρ hρ => CoreSatBy_mono
              (fun id hid => HashSet_contains_insert_fold _ _ _ (Or.inl hid)) hρ) hcv)⟩
      · simp [hc] at hsteps
    | coreRange lo hi =>
      apply ih_rest _ _ hsteps
      exact ⟨hinv.1, hinv.2.1, fun hs ρ hρ => hci hs ρ (CoreSatBy_mono
        (fun id hid => HashSet_contains_insert_fold_if _ _ _ _ hid) hρ), hib, hsg,
        OrdInv_of hoi rfl rfl rfl (fun _ _ _ hcv =>
          coreValidDB_mono_core (fun ρ hρ => CoreSatBy_mono
            (fun id hid => HashSet_contains_insert_fold_if _ _ _ _ hid) hρ) hcv)⟩
    | strengtheningToCore on =>
      cases on
      · apply ih_rest _ _ hsteps
        exact ⟨hinv.1, hinv.2.1, fun hs => absurd hs (by simp), hib, hsg, hoi⟩
      · apply ih_rest _ _ hsteps
        exact ⟨hinv.1, hinv.2.1,
          fun _ ρ hρ id c hget => hρ id c (allIds_contains hget) hget, hib, hsg,
          OrdInv_of hoi rfl rfl rfl (fun _ _ _ hcv => coreValidDB_mono_core
            (fun ρ hρ id c _ hget => hρ id c (allIds_contains hget) hget) hcv)⟩
    | loadOrder name lits =>
      cases name with
      | none =>
        by_cases hord : state.ord.isSome = true
        · simp only [hord, ↓reduceIte] at hsteps
          apply ih_rest _ _ hsteps
          exact ⟨hinv.1, hinv.2.1, hci, hib, hsg, OrdInv_of_none rfl⟩
        · simp only [hord, Bool.false_eq_true, ↓reduceIte] at hsteps; simp at hsteps
      | some name =>
        simp only [] at hsteps
        cases hl : loadOrderStep state name lits with
        | none => rw [hl] at hsteps; simp at hsteps
        | some st =>
          rw [hl] at hsteps
          obtain ⟨O, z, hmem, hzl, hza, rfl⟩ := loadOrderStep_spec state name lits st hl
          apply ih_rest _ _ hsteps
          refine ⟨hinv.1, hinv.2.1,
            fun _ ρ hρ id c hget => hρ id c (allIds_contains hget) hget, hib, hsg, ?_⟩
          intro O' z' hoz
          simp only [Option.some.injEq, Prod.mk.injEq] at hoz
          obtain ⟨rfl, rfl⟩ := hoz
          have hg := hsg _ hmem
          exact ⟨hg, hzl, hza, coreValid_iff_DB.mpr (coreValidDB_allIds hg.refl hzl)⟩
    | defOrder od =>
      match fuel with
      | 0 => simp at hsteps
      | n + 1 =>
        simp only [] at hsteps
        cases hd : defOrderStep (execStepsFuel n) state od with
        | none => rw [hd] at hsteps; simp at hsteps
        | some st =>
          rw [hd] at hsteps
          obtain ⟨O, hgood, rfl⟩ := defOrderStep_spec _ (hexecN n) (hmonoN n)
            state od st hd
          apply ih_rest _ _ hsteps
          refine ⟨hinv.1, hinv.2.1, hci, hib, ?_, hoi⟩
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hgood
          · exact hsg p hp
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
      match hchk : checkSolutionVals state.origConstrs state.objective
          state.curObj lits with
      | none => simp [hchk] at hsteps
      | some (bo, bc) =>
        by_cases hv : solValueOk state.curOffset bc value = false
        · simp [hchk, hv] at hsteps
        simp [hchk, hv] at hsteps
        apply ih_rest _ _ hsteps
        obtain ⟨ρ, hρ, hvo, _⟩ := checkSolutionVals_sound _ _ _ _ _ _ hchk
        have hbw := BestWitnessed_updBestWit state.chk _ ρ hinv.2.1 hρ
        simp only [opbVal, hvo] at hbw
        exact ⟨fun v hF himp =>
          hinv.1 v hF (Improving_updBest _ _ _ himp).2, hbw, hci, hib, hsg, hoi⟩
    | soli lits value =>
      match hchk : checkSolutionVals state.origConstrs state.objective
          state.curObj lits with
      | none => simp [hchk] at hsteps
      | some (bo, bc) =>
        by_cases hv : solValueOk state.curOffset bc value = false
        · simp [hchk, hv] at hsteps
        simp [hchk, hv] at hsteps
        apply ih_rest _ _ hsteps
        obtain ⟨ρ, hρ, hvo, hvc⟩ := checkSolutionVals_sound _ _ _ _ _ _ hchk
        have hbw := BestWitnessed_updBestWit state.chk _ ρ hinv.2.1 hρ
        simp only [opbVal, hvo] at hbw
        refine ⟨fun v hF himp => ?_, hbw,
          fun hs => coreImplied_insert_core
            (IdsBelowDb_fresh hib (Nat.le_refl _)) (hci hs),
          IdsBelowDb_insert hib (Nat.lt_succ_self _) (Nat.le_succ _), hsg,
          OrdInv_of hoi rfl rfl rfl (fun _ _ _ hcv => coreValidDB_insert_bound
            (IdsBelowDb_fresh hib (Nat.le_refl _)) (fun ρ ρ' hle hc =>
              negObj_sat_mono state.curObj _ ρ ρ'
                (by simp only [opbVal] at hle; omega) hc) hcv)⟩
        obtain ⟨hlt, himp0⟩ := Improving_updBest _ _ _ himp
        obtain ⟨w, hw, hle⟩ := hinv.1 v hF himp0
        refine ⟨w, fun id' c' hget => ?_, hle⟩
        rw [HashMap_get?_insert] at hget
        by_cases heq : state.nextId == id'
        · simp [heq] at hget; subst hget
          -- w satisfies the improvement constraint:
          -- objVal curObj w + curOffset ≤ opbVal v < bc + curOffset
          apply improveConstr_sat_of_lt
          · rw [← hvc]
            exact Sat.PB.evalSum_le_coeffSumR ρ state.curObj
          · simp only [opbVal] at hle hlt
            omega
        · simp [heq] at hget; exact hw id' c' hget
    | obji v =>
      by_cases hno : (!state.hasObj) = true
      · simp [hno] at hsteps
      simp only [hno, Bool.false_eq_true, ↓reduceIte] at hsteps
      apply ih_rest _ _ hsteps
      refine ⟨fun u hF himp => ?_, hinv.2.1,
        fun hs => coreImplied_insert_core
          (IdsBelowDb_fresh hib (Nat.le_refl _)) (hci hs),
        IdsBelowDb_insert hib (Nat.lt_succ_self _) (Nat.le_succ _), hsg,
        OrdInv_of hoi rfl rfl rfl (fun _ _ _ hcv => coreValidDB_insert_bound
          (IdsBelowDb_fresh hib (Nat.le_refl _)) (fun ρ ρ' hle hc =>
            negObj_sat_mono state.curObj _ ρ ρ'
              (by simp only [opbVal] at hle; omega) hc) hcv)⟩
      obtain ⟨hlt, himp0⟩ := Improving_updBest _ _ _ himp
      obtain ⟨w, hw, hle⟩ := hinv.1 u hF himp0
      refine ⟨w, fun id' c' hget => ?_, hle⟩
      rw [HashMap_get?_insert] at hget
      by_cases heq : state.nextId == id'
      · simp [heq] at hget; subst hget
        exact objiConstr_sat_of_lt _ _ _ _ (Int.lt_of_le_of_lt hle hlt)
      · simp [heq] at hget; exact hw id' c' hget
    | eobj pobj =>
      by_cases he : eobjOk state.hasObj state.curObj state.curOffset pobj = true
      · simp only [he, ↓reduceIte] at hsteps; exact ih_rest state hinv hsteps
      · simp [he] at hsteps
    | obju kind pobj sub =>
      cases sub with
      | none => simp at hsteps
      | some sp =>
        obtain ⟨items, qedHint⟩ := sp
        match fuel with
        | 0 => simp at hsteps
        | n + 1 =>
          simp only [] at hsteps
          cases ho : objuStep (execStepsFuel n) state kind pobj items.toList
              qedHint with
          | none => rw [ho] at hsteps; simp at hsteps
          | some st =>
            rw [ho] at hsteps
            obtain ⟨hkeep, hdb, heq⟩ := objuStep_sound (execStepsFuel n)
              (hexecN n) state kind pobj _ _ st ho
            obtain ⟨-, hcore, hs2c, hnext, hordst, hords⟩ := objuStep_shape
              (execStepsFuel n) (hmonoN n) state kind pobj _ _ st ho
            refine hstep st hkeep (fun w hw => ⟨w, by rw [hdb]; exact hw,
              Int.le_of_eq (heq w (CoreSatBy_of_DBSatBy hw))⟩) ?_ ?_
              (StoredGood_of hords hsg) ?_ hsteps
            · intro hs
              rw [hdb, hcore]
              exact hci (hs2c ▸ hs)
            · rw [hdb]
              exact IdsBelowDb_mono hib hnext
            · -- the objectives agree on core models: the argument of
              -- `Dominance.coreValid_obj_eq`, done directly on the
              -- hash-map form
              intro O z hoz
              have hoz' : state.ord = some (O, z) := hordst.symm.trans hoz
              obtain ⟨hgo, hz, hza, hcv⟩ := hoi O z hoz'
              refine ⟨hgo, hz, hza, coreValid_iff_DB.mpr ?_⟩
              have hcv' := coreValid_iff_DB.mp hcv
              rw [hdb, hcore]
              intro ρ hρ
              obtain ⟨ρ', h1, h2, h3⟩ := hcv' ρ hρ
              refine ⟨ρ', h1, h2, ?_⟩
              rw [heq ρ hρ, heq ρ' (CoreSatBy_of_DBSatBy h1)]
              exact h3
    | conclusionSat _ => exact ih_rest state hinv hsteps
    | conclusionBounds _ _ _ _ => exact ih_rest state hinv hsteps
    | outputClaim _ _ => exact ih_rest state hinv hsteps
    | _ => simp at hsteps

/-- Main step lemma: execution preserves the optimization invariant. -/
theorem execStepsFuel_inv_preserve (fuel : Nat)
    (state state' : BoolCheckState) (steps : List PBCatcher.ProofStep)
    (hinv : StateInv state)
    (hsteps : execStepsFuel fuel state steps = some state') :
    StateInv state' :=
  (execStepsFuel_inv_preserve_fields fuel state state' steps hinv hsteps).1

/-- Execution from the initial state of `F` and `obj`, ending with a
contradiction in the database, proves that no solution of `F` lies below
the threshold `best`. With no logged value (no `sol`, `soli` or `obji`:
`best = none`), `F` is unsatisfiable. -/
theorem execStepsFuel_no_improving (fuel : Nat) (F : Array Constr)
    (numVars : Nat) (obj : Objective) (offset : Int)
    (steps : List PBCatcher.ProofStep) (s : BoolCheckState)
    (hexec : execStepsFuel fuel
      (BoolCheckState.fromConstrs F numVars obj offset) steps = some s)
    (id : Nat) (c : Constr) (hc : s.db.get? id = some c)
    (hcontra : c.isContra = true) :
    (∀ v, FormulaSat F v → ¬ Improving obj offset s.best v) ∧
      BestWitnessed F obj offset s.bestWit := by
  obtain ⟨hinv, hF, hO, hOff⟩ := execStepsFuel_inv_preserve_fields fuel _ s
    steps (StateInv_init F numVars obj offset) hexec
  have hF' : s.origConstrs = F := hF
  have hO' : s.objective = obj := hO
  have hOff' : s.offset = offset := hOff
  obtain ⟨hdbopt, hbw, -⟩ := hinv
  rw [hF', hO', hOff'] at hdbopt hbw
  refine ⟨fun v hv himp => ?_, hbw⟩
  obtain ⟨w, hw, _⟩ := hdbopt v hv himp
  exact contra_unsat c w (by simpa [Constr.isContra] using hcontra) (hw id c hc)

/-- Bounds corollary: a contradiction in the final database with threshold
and witnessed value both `b` proves that `b` is the optimum of the OPB
objective `opbVal obj offset`: every solution of `F` has value at least
`b`, and some solution attains `b`. -/
theorem execStepsFuel_bounds (fuel : Nat) (F : Array Constr) (numVars : Nat)
    (obj : Objective) (offset : Int) (steps : List PBCatcher.ProofStep)
    (s : BoolCheckState)
    (hexec : execStepsFuel fuel
      (BoolCheckState.fromConstrs F numVars obj offset) steps = some s)
    (id : Nat) (c : Constr) (hc : s.db.get? id = some c)
    (hcontra : c.isContra = true) (b : Int) (hb : s.best = some b)
    (hbw : s.bestWit = some b) :
    (∀ v, FormulaSat F v → b ≤ opbVal obj offset v) ∧
      (∃ ρ, FormulaSat F ρ ∧ opbVal obj offset ρ = b) := by
  obtain ⟨hno, hwit⟩ := execStepsFuel_no_improving fuel F numVars obj offset
    steps s hexec id c hc hcontra
  refine ⟨fun v hv => Int.not_lt.mp fun hlt => hno v hv ?_, hwit b hbw⟩
  intro b' hb'
  rw [hb] at hb'
  cases hb'
  exact hlt

theorem checkProof_sound (constrs : Array Constr) (numVars : Nat)
    (objective : Objective) (names : List (String × Nat)) (proofStr : String)
    (h : checkProofBool constrs numVars objective names proofStr = true) :
    formulaUnsat constrs := by
  unfold checkProofBool at h
  match hparse : PBCatcher.parseVeriPBProofWith
      (PBCatcher.VarTable.ofList names numVars) proofStr with
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
      · rename_i o id _
        simp only [Bool.and_eq_true] at hpi
        obtain ⟨_, hpi⟩ := hpi
        split at hpi
        · rename_i c hdb
          have hno := (execStepsFuel_no_improving _ constrs _ objective _
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
(`PBCatcher.OPBObjective`). For `max: f` the parser negates the objective, as
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

/-- A database constraint implying `curObj ≥ lb − curOffset` over the
current objective, with `lb` at most the threshold: `lb` is a lower bound
on the original OPB objective. Improving solutions have a database
counterpart (`DBOpt`) that satisfies the implied bound; the others are
bounded by the threshold. -/
theorem StateInv_lower {s : BoolCheckState} (hinv : StateInv s)
    {id : Nat} {D : Constr} (hD : s.db[id]? = some D) (l : Int)
    (hbest : ∀ b, s.best = some b → l ≤ b)
    (himpl : impliesSyntactic (PBCatcher.normalizeConstr D)
      (PBCatcher.normalizeConstr (lowerBoundConstr s.curObj s.curOffset l))
      = true) :
    ∀ v, FormulaSat s.origConstrs v → l ≤ opbVal s.objective s.offset v := by
  intro v hv
  by_cases himp : Improving s.objective s.offset s.best v
  · obtain ⟨w, hw, hle⟩ := hinv.1 v hv himp
    have hDw : D.sat w := hw id D (by rw [Std.HashMap.get?_eq_getElem?]; exact hD)
    have hT := normalize_sat_rev _ w
      (impliesSyntactic_sound _ _ w himpl (normalize_sat D w hDw))
    simp only [lowerBoundConstr, Constr.sat] at hT
    simp only [opbVal, objVal] at hle ⊢
    have := Int.self_le_toNat (l - s.curOffset)
    have : (((l - s.curOffset).toNat : Nat) : Int) ≤
        (Sat.PB.evalSum w s.curObj : Int) :=
      Int.ofNat_le.mpr hT
    omega
  · simp only [Improving, Classical.not_forall] at himp
    obtain ⟨b, hb, hnlt⟩ := himp
    have := hbest b hb
    omega

theorem lowerBoundOk_sound {s : BoolCheckState} (hinv : StateInv s)
    (lb : Option Int) (hint : Option Nat)
    (h : lowerBoundOk (fun id => s.db[id]?) s.curObj s.curOffset s.best lb
      hint = true) :
    formulaLowerBound s.origConstrs s.objective s.offset lb := by
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
        refine StateInv_lower hinv hD l (fun b hb' => ?_) himpl
        rw [hb'] at hb
        simpa using hb

theorem upperBoundOk_sound (F : Array Constr) (obj : Objective)
    (offset : Int) (bestWit : Option Int) (ub : Option Int)
    (lits : Option (List PBCatcher.OPBLit))
    (hbw : BestWitnessed F obj offset bestWit)
    (h : upperBoundOk F obj offset bestWit ub lits = true) :
    formulaUpperBound F obj offset ub := by
  cases ub with
  | none => trivial
  | some u =>
    simp only [formulaUpperBound]
    cases lits with
    | none =>
      cases hb : bestWit with
      | none => simp [upperBoundOk, hb] at h
      | some b =>
        simp only [upperBoundOk, hb, decide_eq_true_eq] at h
        obtain ⟨ρ, hρ, hval⟩ := hbw b hb
        simp only [opbVal] at hval
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
    (step : PBCatcher.ProofStep) (claim : Claim)
    (h : conclusionClaim (fun id => s.db[id]?) s.origConstrs s.conclCtx step
      = some claim) :
    claim.holds s.origConstrs s.objective s.offset := by
  cases step with
  | conclusion id =>
    cases hc : s.db[id]? with
    | none => simp [conclusionClaim, hc] at h
    | some c =>
      by_cases hcon : c.isContra = true
      · cases hb : s.best with
        | none =>
          simp only [conclusionClaim, BoolCheckState.conclCtx, hc, hcon, hb,
            if_true, Option.some.injEq] at h
          subst h
          exact formulaUnsat_of_forall (StateInv_unsat hinv hb hc hcon)
        | some b => simp [conclusionClaim, BoolCheckState.conclCtx, hc, hcon, hb] at h
      · simp [conclusionClaim, hc, hcon] at h
  | conclusionSat lits =>
    by_cases hs : satOk s.origConstrs s.objective s.bestWit lits = true
    · simp only [conclusionClaim, BoolCheckState.conclCtx, hs, if_true,
        Option.some.injEq] at h
      subst h
      simp only [Claim.holds, formulaSatisfiable]
      cases lits with
      | none =>
        simp only [satOk] at hs
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨ρ, hρ, _⟩ := hinv.2.1 b hb
        exact ⟨ρ, hρ⟩
      | some ls =>
        simp only [satOk] at hs
        obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨ρ, hρ, _⟩ := checkSolution_sound _ _ ls val hval
        exact ⟨ρ, hρ⟩
    · simp [conclusionClaim, BoolCheckState.conclCtx, hs] at h
  | conclusionBounds lb hint ub lits =>
    by_cases hok : (lowerBoundOk (fun id => s.db[id]?) s.curObj s.curOffset
        s.best (boundOpt lb) hint &&
        upperBoundOk s.origConstrs s.objective s.offset s.bestWit
          (boundOpt ub) lits) = true
    · simp only [conclusionClaim, BoolCheckState.conclCtx] at h
      rw [if_pos hok, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hok
      exact ⟨lowerBoundOk_sound hinv _ hint hok.1,
        upperBoundOk_sound _ _ s.offset _ _ lits hinv.2.1 hok.2⟩
    · simp only [conclusionClaim, BoolCheckState.conclCtx] at h
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
  match hparse : PBCatcher.parseVeriPBProofWith
      (PBCatcher.VarTable.ofList names numVars) proofStr with
  | .error _ => simp [hparse] at h
  | .ok proofData =>
    simp only [hparse] at h
    match hexec : execStepsFuel (pbcDepth proofData.steps.toList + 1)
        (BoolCheckState.fromConstrs constrs (max numVars proofData.numVars)
          objective offset)
        proofData.steps.toList with
    | some s =>
      simp only [hexec] at h
      obtain ⟨hinv, hF, hO, hOff⟩ := execStepsFuel_inv_preserve_fields _ _ s _
        (StateInv_init constrs _ objective offset) hexec
      have hF' : s.origConstrs = constrs := hF
      have hO' : s.objective = objective := hO
      have hOff' : s.offset = offset := hOff
      match hlast : lastFooter proofData.steps with
      | some (o, step) =>
        simp only [hlast] at h
        by_cases ho : outputClaimOk s.conclCtx o = true
        · rw [if_pos ho] at h
          rw [← hF'] at h
          rw [← hF', ← hO', ← hOff']
          exact conclusionClaim_sound s hinv step claim h
        · rw [if_neg ho] at h
          cases h
      | none => simp [hlast] at h
    | none => simp [hexec] at h

/-- Soundness of the Boolean entry point used by `veripb_reflect` and the
application commands (`mkClaimProof`) for every claim kind, originally for SAT
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
written `x<N>` with their indices (`PBCatcher.OPBInstance.names`, default
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

/-- A note for an `output` claim other than `NONE` in the proof text: the
claim about the output formula is not certified (the theorem is the
conclusion's; `outputClaimOk` checks the bound side only). -/
private def outputClaimNote (proofStr : String) : String :=
  let ls := (proofStr.splitOn "\n").filterMap fun l =>
    let t := l.trimAscii.toString
    if t.startsWith "output" then some t else none
  match ls.getLast? with
  | some t =>
    let r := ((t.drop "output".length).trimAscii.toString)
    if r.startsWith "NONE" then "" else
      s!" [output claim {((r.splitOn ";").headD r).trimAscii.toString} not certified]"
  | none => ""

/-- `veripb_reflect name "file.opb" "proof.pbp"` checks a VeriPB kernel proof
by reflection (native evaluation of the checker, `nativeEqTrue`: one per-use
axiom `_native.veripb_reflect.ax_*`, as `native_decide`; see
`mkFormulaUnsatProof`) and registers a theorem matching the proof's conclusion (which
must close the proof: `output ... ; conclusion ... ; end pseudo-Boolean
proof ;`; an output claim `output DERIVABLE|EQUISATISFIABLE|EQUIOPTIMAL
FILE` is accepted when its bound-side preconditions hold, `outputClaimOk`,
but is not certified: the theorem is the conclusion's):
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
    let inst ← match PBCatcher.parseOPBNamed opbStr with
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
    let maxNote := (if fromMax then
      " [max: objective, bounds on its negation]" else "") ++
      outputClaimNote proofStr
    -- UNSAT without solution logging: the established `checkProofBool` path
    if lastConclusionIsUnsat proofStr then
      if let some proof ← mkFormulaUnsatProof? `veripb_reflect
          constrsExpr numVarsExpr proofStr (some (← getRef)) objExpr inst.names then
        register (mkApp (mkConst ``formulaUnsat) constrsExpr) proof
          ("formulaUnsat" ++ outputClaimNote proofStr)
        return
      -- rejected: `proofClaim?` below rejects it too (`hasUnsatConclusion`
      -- and the `.unsat` claim use the same footer rule; they can only
      -- differ if the text scan and the parser disagree on the conclusion)
    match proofClaim? inst.constrs inst.numVars objective offset inst.names
        proofStr with
    | none => throwError "VeriPB reflection checker rejected the proof"
    | some claim =>
      let proof ← mkClaimProof `veripb_reflect constrsExpr numVarsExpr objExpr
        offsetExpr proofStr claim (ref? := some (← getRef)) (names := inst.names)
      let what := match claim with
        | .unsat => "formulaUnsat" ++ outputClaimNote proofStr
        | .sat => "formulaSatisfiable" ++ outputClaimNote proofStr
        | .bounds lb ub =>
          s!"formulaBounds, {showBound lb} ≤ objective ≤ {showBound ub}{maxNote}"
      register (claimTypeExpr constrsExpr objExpr offsetExpr claim) proof what

end PBCatcher.Reflect
