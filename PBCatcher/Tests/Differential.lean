/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import PBCatcher.Reflect

/-!
# Fast checker differential test

`PBCatcher.Reflect.checkProofBool` (verified, List-based) is replaced at
runtime by `PBCatcher.Reflect.Fast.checkProofBoolFast` via `@[implemented_by]`.
The per-use axioms of `veripb_reflect` assert facts about the verified
definition, so the fast checker must accept exactly the same proofs. This
test runs the verified step function `execStepsFuel` and the fast step
function `Fast.execFStepsFuel` side by side, one proof step at a time, and
requires identical constraint databases (ids, terms in order, degrees) after
every step. The verified pipeline itself uses `normalizeConstr`, whose
runtime replacement is checked separately in `Tests/Normalize.lean`.

The same harness on the large `applications/` proofs (up to Paley(101),
62,922 steps) is run before releases; see `applications/difftest.lean`.
-/

namespace PBCatcher.Tests.Differential

open PBCatcher.Reflect

def constrEq (a b : Constr) : Bool :=
  a.degree == b.degree && a.terms.length == b.terms.length &&
    (a.terms.zip b.terms).all fun ((c1, l1), (c2, l2)) => c1 == c2 && l1 == l2

def showConstr (c : Constr) : String :=
  let ts := c.terms.map fun (a, l) => match l with
    | .pos v => s!"{a}·x{v}"
    | .neg v => s!"{a}·~x{v}"
  s!"{ts} ≥ {c.degree}"

def constrListEq (a b : List Constr) : Bool :=
  a.length == b.length && (a.zip b).all fun (x, y) => constrEq x y

/-- Structural equality of two stored orders (`OrderData` derives no `BEq`). -/
def orderEq (a b : Sat.PB.Dominance.OrderData) : Bool :=
  a.left == b.left && a.right == b.right && a.aux == b.aux &&
    constrListEq a.spec b.spec && constrListEq a.defs b.defs

def ordersEq (a b : List (String × Sat.PB.Dominance.OrderData)) : Bool :=
  a.length == b.length && (a.zip b).all fun ((n1, o1), (n2, o2)) => n1 == n2 && orderEq o1 o2

def ordEq : Option (Sat.PB.Dominance.OrderData × List Sat.PB.Literal) →
    Option (Sat.PB.Dominance.OrderData × List Sat.PB.Literal) → Bool
  | none, none => true
  | some (o1, z1), some (o2, z2) => orderEq o1 o2 && z1 == z2
  | _, _ => false

/-- A core id set as a sorted list (insertion order does not matter). -/
def sortedIds (s : Std.HashSet Nat) : List Nat := s.toList.mergeSort (· ≤ ·)

/-- `none` if the two databases agree, otherwise a description of the first
difference found. -/
def dbDiff (slow : Std.HashMap Nat Constr) (fast : Std.HashMap Nat Fast.FConstr) :
    Option String := Id.run do
  if slow.size != fast.size then
    return some s!"db size differs: verified {slow.size} vs fast {fast.size}"
  for (id, c) in slow.toList do
    match fast[id]? with
    | none => return some s!"id {id} missing in fast db"
    | some fc =>
      let fcc := Fast.fromFConstr fc
      if !constrEq c fcc then
        return some s!"id {id} differs:\n  verified {showConstr c}\n  fast     {showConstr fcc}"
  return none

/-- Run both checkers step by step on one instance; throw on any difference.
`fullEvery` controls how often the whole database is compared (every step by
default); in between, only the size and the newly inserted constraint are
compared. If `expectReject = some k`, both checkers must reject step `k`
(and agree on every step before it); the test then stops there. Returns the
claim of the last conclusion step on the final states (`none` after an
expected rejection); the two checkers must agree on it. -/
def runOneClaim (name opbPath proofPath : String) (fullEvery : Nat := 1)
    (expectReject : Option Nat := none) :
    IO (Option Claim) := do
  let opbStr ← IO.FS.readFile opbPath
  let proofStr ← IO.FS.readFile proofPath
  let inst ← match PBCatcher.parseOPBNamed opbStr with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{name}: OPB parse error: {e}")
  let obj : Objective := match inst.objective with
    | some o => o.terms
    | none => []
  let offset : Int := match inst.objective with
    | some o => o.offset
    | none => 0
  let proof ← match PBCatcher.parseVeriPBProofWith
      (PBCatcher.VarTable.ofList inst.names inst.numVars) proofStr with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"{name}: proof parse error: {e}")
  let constrs := inst.constrs
  -- the variable count of `checkProofBool` (fresh proof variables included)
  let numVars := max inst.numVars proof.numVars
  let steps := proof.steps.toList
  let fuel := pbcDepth steps + 1
  let mut slow := BoolCheckState.fromConstrs constrs numVars obj offset
  let mut fast := Fast.FBoolCheckState.fromConstrs constrs numVars obj offset
  if let some msg := dbDiff slow.db fast.db then
    throw (IO.userError s!"{name}: initial state: {msg}")
  let mut k := 0
  for step in steps do
    let rs := execStepsFuel fuel slow [step]
    let rf := Fast.execFStepsFuel fuel fast [step]
    match rs, rf with
    | none, none =>
      if expectReject == some k then
        if (Fast.proofClaimFast? constrs inst.numVars obj offset inst.names
            proofStr).isSome then
          throw (IO.userError s!"{name}: proofClaimFast? accepts a rejected proof")
        IO.println s!"{name}: {k} steps identical, both reject step {k} as expected"
        return none
      throw (IO.userError s!"{name}: both checkers reject step {k}")
    | some _, none =>
      throw (IO.userError s!"{name}: MISMATCH at step {k}: verified accepts, fast rejects")
    | none, some _ =>
      throw (IO.userError s!"{name}: MISMATCH at step {k}: verified rejects, fast accepts")
    | some s, some f =>
      if s.nextId != f.nextId then
        throw (IO.userError s!"{name}: MISMATCH at step {k}: nextId {s.nextId} vs {f.nextId}")
      if s.best != f.best || s.bestWit != f.bestWit then
        throw (IO.userError s!"{name}: MISMATCH at step {k}: best {s.best} vs \
          {f.best}, bestWit {s.bestWit} vs {f.bestWit}")
      if s.offset != f.offset || s.curOffset != f.curOffset ||
          s.curObj != f.curObj || s.chk != f.chk then
        throw (IO.userError s!"{name}: MISMATCH at step {k}: objective fields")
      if s.s2c != f.s2c || sortedIds s.coreIds != sortedIds f.coreIds then
        throw (IO.userError s!"{name}: MISMATCH at step {k}: core sets \
          {sortedIds s.coreIds} vs {sortedIds f.coreIds}")
      if !ordersEq s.orders f.orders || !ordEq s.ord f.ord then
        throw (IO.userError s!"{name}: MISMATCH at step {k}: stored or loaded orders")
      let diff? : Option String := Id.run do
        if s.db.size != f.db.size then
          return some s!"db size differs: verified {s.db.size} vs fast {f.db.size}"
        if s.nextId > slow.nextId then
          let id := s.nextId - 1
          match s.db[id]?, f.db[id]? with
          | some c, some fc =>
            let fcc := Fast.fromFConstr fc
            if !constrEq c fcc then
              return some s!"id {id} differs:\n  verified {showConstr c}\n  \
                fast     {showConstr fcc}"
          | none, none => pure ()
          | _, _ => return some s!"id {id} presence differs"
        if fullEvery != 0 && k % fullEvery == 0 then dbDiff s.db f.db else none
      if let some msg := diff? then
        throw (IO.userError s!"{name}: MISMATCH at step {k}: {msg}")
      slow := s
      fast := f
    k := k + 1
  if let some j := expectReject then
    throw (IO.userError s!"{name}: step {j} accepted, expected rejection")
  if let some msg := dbDiff slow.db fast.db then
    throw (IO.userError s!"{name}: MISMATCH at end: {msg}")
  let okSlow := hasUnsatConclusion proof.steps slow
  let okFast := Fast.hasFUnsatConclusion proof.steps fast
  if okSlow != okFast then
    throw (IO.userError s!"{name}: conclusion differs: verified {okSlow}, fast {okFast}")
  -- the claim of the last conclusion step (SAT, BOUNDS, optimality), as
  -- `proofClaim?` and `Fast.proofClaimFast?` evaluate it on the final states
  let claim? (getC : Nat → Option Constr) (ctx : ConclCtx) : Option Claim :=
    match lastFooter proof.steps with
    | some (o, st) =>
      if outputClaimOk ctx o then conclusionClaim getC constrs ctx st else none
    | none => none
  let cSlow := claim? (fun id => slow.db[id]?) slow.conclCtx
  let cFast := claim? (fun id => (fast.db[id]?).map Fast.fromFConstr)
    { objective := fast.objective, offset := fast.offset, curObj := fast.curObj,
      curOffset := fast.curOffset, best := fast.best, bestWit := fast.bestWit,
      chk := fast.chk }
  if cSlow != cFast then
    throw (IO.userError s!"{name}: claim differs: verified {repr cSlow}, fast {repr cFast}")
  -- the runtime entry point (`proofClaim?` is `@[implemented_by]` it)
  let cRun := Fast.proofClaimFast? constrs inst.numVars obj offset inst.names proofStr
  if cSlow != cRun then
    throw (IO.userError s!"{name}: claim differs: verified {repr cSlow}, \
      proofClaimFast? {repr cRun}")
  -- the UNSAT path agrees with the UNSAT claim
  if okSlow != (cSlow == some Claim.unsat) then
    throw (IO.userError s!"{name}: hasUnsatConclusion {okSlow}, claim {repr cSlow}")
  IO.println s!"{name}: {k} steps identical, conclusion {okSlow}, claim {repr cSlow}"
  return cSlow

/-- `runOneClaim` without the claim. -/
def runOne (name opbPath proofPath : String) (fullEvery : Nat := 1)
    (expectReject : Option Nat := none) : IO Unit :=
  discard <| runOneClaim name opbPath proofPath fullEvery expectReject

/-- `runOneClaim`, and the claim must be `expected`. -/
def runExpect (name opbPath proofPath : String) (expected : Option Claim) :
    IO Unit := do
  let c ← runOneClaim name opbPath proofPath
  if c != expected then
    throw (IO.userError s!"{name}: claim {repr c}, expected {repr expected}")

/-- The proof must be rejected by the parser (and so by the runtime entry
point `proofClaimFast?`). -/
def expectParseError (name opbPath proofPath : String) : IO Unit := do
  let opbStr ← IO.FS.readFile opbPath
  let proofStr ← IO.FS.readFile proofPath
  let inst ← match PBCatcher.parseOPBNamed opbStr with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{name}: OPB parse error: {e}")
  let obj : Objective := match inst.objective with
    | some o => o.terms
    | none => []
  match PBCatcher.parseVeriPBProofWith
      (PBCatcher.VarTable.ofList inst.names inst.numVars) proofStr with
  | .ok _ => throw (IO.userError s!"{name}: parsed, expected a parse error")
  | .error e =>
    if (Fast.proofClaimFast? inst.constrs inst.numVars obj 0 inst.names
        proofStr).isSome then
      throw (IO.userError s!"{name}: proofClaimFast? accepts an unparsable proof")
    IO.println s!"{name}: parse error as expected: {e}"

end PBCatcher.Tests.Differential

open PBCatcher.Tests.Differential PBCatcher.Reflect in
#eval show IO Unit from do
  let d := "PBCatcher/Tests/data/"
  for n in ["php21", "red_subproof", "red_swap", "red_const", "red_neglit", "red_basic",
      "weaken_cases", "rup_cases", "rup_prop", "dup", "dup_pair", "dup_pbc"] do
    runOne n (d ++ n ++ ".opb") (d ++ n ++ "_kernel.pbp")
  -- rup (CakePB semantics: one pass over the hints in order, the negated
  -- target only through an explicit `~`, no hints = reject). rup_prop: one
  -- weighted constraint forces three literals at once; accepted forms: hints
  -- in propagation order, `~` twice, a target with a complementary pair.
  -- Rejected at step 1 by both checkers and by CakePB, accepted by VeriPB
  -- 3.0.1 (fixpoint rounds, implicit `~`, database propagation): hints
  -- reversed (`rup_prop_rev`), no `~` (`rup_prop_implicit`), no hints
  -- (`rup_prop_nohint`). rup_noprop: an unsatisfiable 2-CNF without unit
  -- propagation from the empty assignment; step 2 (`rup >= 1 : 1 2 3 4`)
  -- and the hint-free `rup >= 1 ;` are rejected (also by VeriPB and CakePB).
  for n in ["rup_prop_rev", "rup_prop_implicit", "rup_prop_nohint"] do
    runOne n (d ++ "rup_prop.opb") (d ++ n ++ "_kernel.pbp") (expectReject := some 1)
  runOne "rup_noprop" (d ++ "rup_noprop.opb") (d ++ "rup_noprop_kernel.pbp")
    (expectReject := some 2)
  runOne "rup_noprop_nohint" (d ++ "rup_noprop.opb")
    (d ++ "rup_noprop_nohint_kernel.pbp") (expectReject := some 1)
  -- optimization proofs with solution logging (soli)
  for n in ["vc6_linear", "vc6_sol_soli", "vc6_fakeunsat", "vc6_pbcok", "vc6_redok"] do
    runOne n (d ++ "vc6.opb") (d ++ n ++ "_kernel.pbp")
  -- rejected proofs: both checkers must reject the same step
  for (n, k) in [("vc6_sol_unsat", 3), ("vc6_redsol", 1)] do
    runOne n (d ++ "vc6.opb") (d ++ n ++ "_kernel.pbp") (expectReject := some k)
  -- VeriPB 3 test-suite pairs (Tests/data/v3, kernel proofs by `veripb
  -- --elaborate`). Accepted by CakePB except solution_logging_max_objective
  -- (CakePB cannot parse `max:`).
  -- strengthening_to_core: the witness touches a constraint derived
  -- after `strengthening_to_core on`; database goals range over the core only.
  let v := d ++ "v3/"
  for n in ["all_diff", "card_propagation_assert_negative_rhs",
      "conclusion_BOUNDS_infeasible", "conclusion_SAT_sol_in_proof", "delete_core",
      "delete_core_subproof_rup", "implication_contradiction_source", "implication",
      "input_equality_with_id", "lower_rhs", "rup", "rup_php65",
      "variable_form_division", "normalized_mir_cut", "variable_form_mir_cut",
      "rup_objective_constant_term",
      "solution_logging_improving_optimal_optional_value", "solution_logging_max_objective",
      "solution_logging_optional_value", "strengthening_to_core"] do
    runOne n (v ++ n ++ ".opb") (v ++ n ++ "_kernel.pbp")
  -- `obji` (P2b): the bound comes from the asserted value, the witness from
  -- the conclusion solution
  runExpect "objective_improving" (v ++ "objective_improving.opb")
    (v ++ "objective_improving_kernel.pbp") (some (.bounds (some (-2)) (some (-2))))
  -- `obju`/`eobj` (P2b): objective updates with core-only subproofs
  for n in ["objective_update_subproof", "objective_update_diff_check",
      "objective_update_diff", "conclusion_BOUNDS_objective_change"] do
    runExpect n (v ++ n ++ ".opb") (v ++ n ++ "_kernel.pbp")
      (some (.bounds (some 2) (some 2)))
  runExpect "move_to_core_indexing" (v ++ "move_to_core_indexing.opb")
    (v ++ "move_to_core_indexing_kernel.pbp") none
  -- output claims: accepted as footers (bound-side preconditions), the
  -- theorem is the conclusion's
  runExpect "decision_output" (v ++ "decision_output.opb")
    (v ++ "decision_output_kernel.pbp") none
  for n in ["optimization_output_opposing_lits_objective",
      "optimization_version2_objective_update_output"] do
    runExpect n (v ++ n ++ ".opb") (v ++ n ++ "_kernel.pbp")
      (some (.bounds (some 2) (some 2)))
  -- output claims, bound side (CakePB `check_output` without the output
  -- formula): DERIVABLE needs no logged value, EQUISATISFIABLE no logged and
  -- no witnessed value and checked deletion on, EQUIOPTIMAL checked deletion
  -- on and threshold = witnessed value; IMPLICIT is rejected
  for (o, n, c) in [("vc6.opb", "vc6_out_equiopt", some (Claim.bounds (some 3) (some 3))),
      ("vc6.opb", "vc6_out_derivable_sol", none), ("vc6.opb", "vc6_out_equisat_sol", none),
      ("vc6.opb", "vc6_out_equiopt_delc", none), ("vc6.opb", "vc6_out_implicit", none),
      ("concl/obji3.opb", "obji3_out_equiopt", none),
      ("concl/sat3.opb", "sat3_out_derivable", none), ("concl/sat3.opb", "sat3_out_equisat", none),
      ("concl/sat3.opb", "sat3_out_equisat_sol", some Claim.sat),
      ("concl/sat3.opb", "sat3_out_equiopt", none),  -- EQUIOPTIMAL needs an objective
      ("php21.opb", "php21_out_derivable", some Claim.unsat)] do
    runExpect n (d ++ o) (d ++ "concl/" ++ n ++ ".pbp") c
  -- orders and dominance: def_order, load_order, dom, and red with the
  -- order goals; all accepted by VeriPB 3.0.1 and CakePB
  for n in ["dominance_simple_order", "dominance_with_aux_vars",
      "redundance_non_touching_order", "dominance_load_order_literal"] do
    runOne n (v ++ n ++ ".opb") (v ++ n ++ "_kernel.pbp")
  -- Hand-written tests for the T3 statements (Tests/data/t3). Every accepted
  -- proof is accepted by VeriPB 3.0.1 and CakePB (core_range: VeriPB only,
  -- CakePB cannot parse `core range`); every rejected one is rejected by
  -- CakePB, and by VeriPB except where noted.
  let t := d ++ "t3/"
  for (o, n) in [("base4", "ia_ok"),          -- ia: weaker, scaled, extra literals, saturation
      ("base4", "delc_ok"),                   -- core id, checked delc with qed shortcut / proofgoal #1
      ("base4", "core_range"),                -- core range, deld of derived, plain delc of core
      ("base4", "delc_s2c_qed"),              -- checked delc under strengthening_to_core with qed : id
      ("base4", "red_qed"),                   -- red: top-level pol, qed : id shortcut
      ("base3", "red_toplevel"),              -- red: top-level pol used by a later proofgoal
      ("obj2", "obj_ok"),                     -- objective goal by implication and by proofgoal #2
      ("obj3", "obj_pg2_ok"),                 -- objective goal #2 proved by its proofgoal only
      ("trivpair", "red_trivpair"),           -- db goal 2 x2 2 ~x2 >= 1: trivial by its pair
      ("base3", "red_goal_ok"),               -- positive control of red_goal_nohint
      ("iacost", "ia_cost"),                  -- ia: excess cost s - t, target with ~l for source l
      ("dbgoal", "red_dbgoal_other"),         -- db goal covered by another constraint's proved goal
      ("base4", "delc_s2c_wit")] do           -- checked delc under s2c with a witness and qed : id
    runOne n (t ++ o ++ ".opb") (t ++ n ++ ".pbp")
  for (o, n, k) in [("base4", "ia_bad", 1),   -- not implied
      ("base4", "ia_nohint", 1),              -- no hint (VeriPB searches, CakePB rejects)
      ("base4", "delc_derived", 2),           -- checked delc of a derived constraint
      ("base4", "delc_twoids", 1),            -- two ids with a subproof
      ("base4", "deld_core", 1),              -- deld of a core constraint
      ("base4", "delc_s2c_noqed", 2),         -- s2c without qed : id (VeriPB accepts, F4)
      ("base3", "red_goal_bad", 1),           -- proofgoal derives no contradiction
      ("base3", "red_goal_nohint", 1),        -- proofgoal without qed : id (VeriPB accepts)
      ("obj2", "obj_bad", 1),                 -- objective goal neither implied nor proved
      ("obj3", "obj_pg2_bad", 1),             -- obj_pg2_ok without its proofgoal #2 (VeriPB accepts)
      ("base3", "red_scope_leak", 2),         -- top-level pol on an id of a closed proofgoal
      ("base3", "red_litwit_bad", 1),         -- x1 -> x2: db goal 1 not covered (VeriPB accepts)
      ("base3", "red_pg2_noobj", 1),          -- proofgoal #2 without an objective
      ("base3", "red_pg_unknown", 1),         -- proofgoal #3
      ("base3", "red_pg_missing", 1),         -- proofgoal 9 (no such constraint)
      ("base3", "red_scope", 1),              -- scope leq (VeriPB and CakePB accept: no order)
      ("base3", "red_scope_geq", 1),          -- scope geq
      ("base4", "red_qed_noncontra", 1),      -- qed : 5 names the non-contradictory ¬C
      ("base4", "s2c_red_deld", 3),           -- red result is core under s2c, deld rejects it
      ("base4", "s2c_delc_derived", 3),       -- plain delc under s2c with a derived constraint
                                              -- (VeriPB accepts)
      ("base4", "delc_sub_derived", 2),       -- checked delc subproof uses derived id 5
      ("base4", "core_id_missing", 1),        -- core id 9 (no such constraint)
      ("base4", "core_range_lo", 4)] do       -- core range 5 6 covers 5: deld 5 rejected
    runOne n (t ++ o ++ ".opb") (t ++ n ++ ".pbp") (expectReject := some k)
  -- strengthening_to_core (Tests/data/s2c): `red` database goals range
  -- over the core only while it is on; the "goal already in the database"
  -- lookup sees the whole database (CakePB `check_red`). Verdicts of VeriPB
  -- 3.0.1 / CakePB in the comments; every proof is accepted by VeriPB (it
  -- autoproves missing goals and, F1, does not move constraints to the core).
  let sc := d ++ "s2c/"
  for (o, n) in [("s2c4", "s2c_skip_derived"),  -- derived pol skipped, red result's goal proved
      ("s2c4", "s2c_moved_goal"),               -- red result derived before `on`, its goal proved
      ("s2c_lookup", "s2c_lookup_derived"),     -- core goal equal to a derived constraint
      ("s2c4", "s2c_goal_derived_id")] do       -- proofgoal for a derived id (resolved in the whole db)
    runOne n (sc ++ o ++ ".opb") (sc ++ n ++ ".pbp")
  for (o, n, k) in [("s2c4", "s2c_red_core_nogoal", 4),  -- red result is core: goal 5 missing
      ("s2c4", "s2c_off_derived", 5),           -- after `off` the derived pol needs a goal
      ("s2c4", "s2c_moved_nogoal", 3)] do       -- `on` moved the red result to the core
    runOne n (sc ++ o ++ ".opb") (sc ++ n ++ ".pbp") (expectReject := some k)
  -- orders (Tests/data/order; all on ord4.opb). Verdicts of VeriPB
  -- 3.0.1 / CakePB in the comments. order_ok defines lex2 (no aux) and
  -- ordaux (spec block, fresh aux lists), loads, unloads, reloads with a
  -- negated literal, unloads, then runs a `red` (both accept).
  let od := d ++ "order/"
  runOne "order_ok" (od ++ "ord4.opb") (od ++ "order_ok.pbp")
  -- accepted by both: a spec block with one red (positive control for
  -- order_spec_noacc), a def_order while an order is loaded, and the same
  -- name defined twice where only the newest definition fits `load_order`
  for n in ["order_spec_one", "order_loaded_def", "order_redef_last",
      "order_red_loaded"] do  -- `red` with an untouched witness while loaded
    runOne n (od ++ "ord4.opb") (od ++ n ++ ".pbp")
  -- parse errors (CakePB parity): no reflexivity block (VeriPB accepts),
  -- `=` in def (both reject), a `pol` in the spec block (both reject)
  for n in ["order_noreflex", "order_eq_def", "order_spec_pol"] do
    expectParseError n (od ++ "ord4.opb") (od ++ n ++ ".pbp")
  for (n, k) in [("order_trans_fresh", 1),  -- fresh_right u1 u2 (w := u): CakePB
                                            -- `check_ws` rejects, VeriPB accepts
      ("order_trans_fail", 1),              -- proofgoal #1 derives no contradiction (both reject)
      ("order_refl_sees_trans", 1),         -- reflexivity proof uses a transitivity premise id (both reject)
      ("order_spec_noacc", 1),              -- second spec red leaves the first spec goal unproved (both reject)
      ("order_load_arity", 2),              -- one literal for two left variables (both reject)
      ("order_load_aux", 2),                -- literal over the aux variable $a1 (both reject)
      ("order_unload_none", 2)] do          -- `load_order ;` with no order loaded
                                            -- (CakePB rejects, VeriPB accepts)
    runOne n (od ++ "ord4.opb") (od ++ n ++ ".pbp") (expectReject := some k)
  -- dominance (Tests/data/dom). lex2 (no aux) on sym4.opb, leaux (one
  -- bit, aux $a with a spec block) on dom3.opb, lex2 with an objective on
  -- obj3b.opb (obj3c.opb: the objective goal fails). Verdicts of VeriPB
  -- 3.0.1 / CakePB in the comments.
  let dd := d ++ "dom/"
  -- accepted by both
  for (o, n) in [("sym4", "dom_simple"),        -- strict goal proved outside any scope
      ("sym4", "dom_strict_geq"),               -- strict goal proved in scope geq
      ("sym4", "dom_qed"),                      -- two doms closed by qed : id
      ("sym4", "dom_s2c"),                      -- dom under strengthening_to_core
      ("sym4", "dom_deld"),                     -- without s2c the dom result is derived (deld)
      ("dom3", "dom_aux_scopes"),               -- order goal and core goal in scope leq, strict in geq
      ("dom3", "dom_aux_outside"),              -- core goal proved outside any scope
      ("dom3", "dom_aux_extra_db"),             -- twin of dom_aux_fresh_db without the aux variable
      ("obj3b", "dom_obj"),                     -- objective goal proved outside any scope
      ("obj3b", "dom_obj_leq"),                 -- objective goal proved in scope leq
      ("dom4", "dom_aux_scopes4"),              -- dom_aux_scopes on dom4 (x4 unconstrained)
      ("dom3", "dom_aux_qed"),                  -- closed by qed : id, no aux variable anywhere
      ("dom3", "dom_aux_extra_db_qed"),         -- twin of dom_aux_fresh_db_qed without the aux variable
      ("dom3", "dom_two_leq"),                  -- two scope leq blocks and a scope geq block
      ("domobj4", "dom_obj_nofresh")] do        -- twin of dom_aux_fresh_obj with x4 for $a
    runOne n (dd ++ o ++ ".opb") (dd ++ n ++ ".pbp")
  -- scope inside a scope (both reject)
  expectParseError "dom_nested_scope" (dd ++ "sym4.opb") (dd ++ "dom_nested_scope.pbp")
  for (o, p, n, k) in [("sym4", "dom_nostrict", "dom_nostrict", 3),  -- strict goal missing (both reject)
      ("sym4", "dom_noorder", "dom_noorder", 2),           -- no order loaded (both reject)
      ("sym4", "dom_unloaded", "dom_unloaded", 4),         -- order unloaded before the dom (both reject)
      ("sym4", "dom_strict_leq", "dom_strict_leq", 3),     -- strict goal proved in scope leq (both reject)
      ("sym4", "dom_qed_scope", "dom_qed_scope", 3),       -- qed : id names a scope-derived id (both reject)
      ("sym4", "dom_s2c_deld", "dom_s2c_deld", 5),         -- under s2c the dom result is core (both reject)
      ("dom3", "dom_aux_core_geq", "dom_aux_core_geq", 3), -- core goal proved in scope geq (both reject)
      ("dom3", "dom_aux_core_missing", "dom_aux_core_missing", 3),  -- core goal missing
                                                           -- (CakePB rejects, VeriPB autoproves)
      ("dom3", "dom_aux_order_geq", "dom_aux_order_geq", 3),  -- order goal proved in scope geq (both reject)
      ("dom3", "dom_aux_fresh_db", "dom_aux_fresh_db", 4),  -- aux variable in a database constraint
                                                           -- (CakePB rejects, VeriPB accepts)
      ("dom4", "dom_aux_fresh_wit", "dom_aux_fresh_wit", 3),  -- witness entry x4 -> $a (F4; twin of
                                                           -- dom_aux_scopes4; CakePB rejects, VeriPB accepts)
      ("dom3", "dom_aux_fresh_c", "dom_aux_fresh_c", 3),   -- aux variable in the dom constraint (F2;
                                                           -- twin dom_aux_qed; CakePB rejects, VeriPB accepts)
      ("dom3", "dom_aux_fresh_db_qed", "dom_aux_fresh_db_qed", 4),  -- aux variable in a database
                                                           -- constraint, dom closed by qed : id (F1 is
                                                           -- checked anyway; CakePB rejects, VeriPB accepts)
      ("domobj4", "dom_aux_fresh_obj", "dom_aux_fresh_obj", 7),  -- aux variable in the objective after
                                                           -- obju (F3; CakePB rejects, VeriPB accepts)
      ("obj3b", "dom_obj_geq", "dom_obj_geq", 3),          -- objective goal proved in scope geq (both reject)
      ("obj3b", "dom_obj_missing", "dom_obj_missing", 3),  -- objective goal missing
                                                           -- (CakePB rejects, VeriPB autoproves)
      ("obj3c", "dom_obj", "dom_obj_fail", 3)] do          -- objective goal fails (both reject)
    runOne n (dd ++ o ++ ".opb") (dd ++ p ++ ".pbp") (expectReject := some k)
  -- redundance and deletion under a loaded order (Tests/data/order).
  -- lex2 on red3.opb / delc2.opb / objord3.opb (loaded x1 x2), leaux (aux
  -- $a, spec block) on aux3.opb (loaded x1), lex1 on lex1x2.opb (x1) and
  -- objred4.opb (x4). Verdicts of VeriPB 3.0.1 / CakePB in the comments.
  for (o, n) in [("red3", "red_ord_goal"),     -- order goal #2 proved outside any scope
      ("red3", "red_ord_untouched"),            -- witness untouched by the order: no order goal
      ("red3", "red_ord_identity"),             -- identity entry x1 -> x1 touches; trivial order goal
      ("aux3", "red_ord_scope"),                -- order goal #2 and db goal 2 proved in scope leq
      ("aux3", "red_ord_scope_extra"),          -- twin of red_ord_scope_auxdb without the aux
      ("aux3", "red_ord_qed_auxdb"),            -- $a in a derived constraint, red closed by qed : id:
                                                -- freshness skipped (CakePB)
      ("aux3", "red_ord_identity_aux_ok"),      -- identity entry x1 -> x1 touches, order goal #2
                                                -- proved in scope leq (both accept)
      ("aux3", "delc_ord_auxdb_ok"),            -- twin of delc_ord_auxdb without the aux
                                                -- (both accept)
      ("delc2", "delc_ord_goal"),               -- checked delc, order goal #2 proved
      ("red3", "delc_ord_unchecked_core"),      -- plain delc while loaded, every constraint core
      ("red3", "delc_ord_unchecked_derived_ok"),  -- the derived constraint deleted first (deld)
      ("objord3", "obju_ord"),                  -- obju while loaded (goal #2 over the core), then red
      ("lex1x2", "red_ord_unsound_dom"),        -- positive control of red_ord_unsound: the dom alone
      ("objred4", "red_ord_obj"),               -- objective goal #3 (= #k+2) proved
      ("objconst3", "obju_const")] do           -- obju to the constant 0, then red (no order)
    runOne n (od ++ o ++ ".opb") (od ++ n ++ ".pbp")
  for (o, n, k) in [("red3", "red_ord_goal_missing", 3),  -- order goal #2 missing
                                                -- (CakePB rejects, VeriPB autoproves)
      ("aux3", "red_ord_scope_geq", 3),         -- scope geq in a red (both reject)
      ("aux3", "red_ord_scope_noorder", 3),     -- order goal #2 missing (both reject)
      ("aux3", "red_ord_scope_auxdb", 4),       -- $a in a derived constraint, red with a scope (F1;
                                                -- CakePB rejects, VeriPB accepts)
      ("aux3", "red_ord_identity_aux", 3),      -- identity entry x1 -> x1 touches, the non-trivial
                                                -- order goal #2 missing (CakePB rejects, VeriPB
                                                -- autoproves)
      ("aux3", "delc_ord_auxdb", 4),            -- $a in a derived constraint, touching checked delc
                                                -- of core constraint 1 with goal #2 proved: F1
                                                -- runs over the database minus the deleted id,
                                                -- derived constraints included (CakePB rejects,
                                                -- VeriPB accepts)
      ("delc2", "delc_ord_missing", 3),         -- checked delc without the order goal
                                                -- (CakePB rejects, VeriPB autoproves)
      ("red3", "delc_ord_unchecked_derived", 4),  -- plain delc while loaded with a derived
                                                -- constraint (CakePB rejects, VeriPB accepts)
      ("objord3", "obju_ord_fail", 3),          -- obju to x1 + x3: goal #2 fails (both reject)
      ("lex1x2", "red_ord_unsound", 3),         -- red x1 >= 1 : x1 -> 1 raises the order key; an
                                                -- order-unaware red would let the dom and rup
                                                -- prove UNSAT of a satisfiable formula (both reject)
      ("objred4", "red_ord_obj_wrongid", 3),    -- the objective goal proved as #2 (the order
                                                -- goal): #3 uncovered (CakePB rejects, VeriPB
                                                -- autoproves)
      ("objconst3", "obju_const_goal", 2)] do   -- known difference: after obju to a constant the
                                                -- objective has no terms and #2 is no goal id
                                                -- (both references accept the trivial goal)
    runOne n (od ++ o ++ ".opb") (od ++ n ++ ".pbp") (expectReject := some k)
  -- pol cuts `k c`, `k n`, `k m` (Tests/data/polcut, written by
  -- testcampaign/t3b/handgen.py). polcut_ok applies every cut to five
  -- constraints (negative variable-form degree, remainder 0, k = 1, k above
  -- every coefficient) for k in {1,2,3,4,8} and checks each result with `ia`
  -- against CakePB's value; the polcut_unsat proofs refute a constraint
  -- together with the negation of one of its cuts. All accepted by VeriPB
  -- 3.0.1 and CakePB. Rejected by all three: k = 0, and `ia` of a result
  -- one degree stronger than CakePB's.
  let pc := d ++ "polcut/"
  runOne "polcut_ok" (pc ++ "polcut.opb") (pc ++ "polcut_ok.pbp")
  for n in ["polcut_unsat_c", "polcut_unsat_n", "polcut_unsat_m"] do
    runOne n (pc ++ n ++ ".opb") (pc ++ n ++ ".pbp")
  for op in ["c", "n", "m"] do
    runOne s!"polcut_k0_{op}" (pc ++ "polcut.opb") (pc ++ s!"polcut_k0_{op}.pbp")
      (expectReject := some 1)
    runOne s!"polcut_strong_{op}" (pc ++ "polcut.opb") (pc ++ s!"polcut_strong_{op}.pbp")
      (expectReject := some 2)
  -- Known deviation (degrees are natural numbers): `2 c` on
  -- `~x1 + ~x2 + ~x3 >= 0` gives `>= -1` in VeriPB and CakePB and `>= 0`
  -- here; adding `x5 >= 1` then gives `x5 >= 0` there and `x5 >= 1` here, so
  -- the final `ia x5 >= 1` is accepted here and rejected by both references
  -- (sound: it is the input constraint 6).
  runOne "polcut_clamp" (pc ++ "polcut.opb") (pc ++ "polcut_clamp.pbp")
  -- Conclusions SAT and BOUNDS, solution values and the objective offset
  -- (Tests/data/concl, P2a). The expected claim is PBLean's verdict; every
  -- verdict agrees with CakePB (cake_pb, CakeML master 2026-10-21), and with
  -- VeriPB 3.0.1 except where noted.
  let cd := d ++ "concl/"
  let some3 : Option Int := some 3
  for (o, n, c) in [
      -- vc6.opb (min: x1 + ... + x6, optimum 3, offset 0)
      ("vc6.opb", "vc6_bounds_nolits", some (Claim.bounds some3 some3)), -- ub = logged best
      ("vc6.opb", "vc6_bounds_noub", some (Claim.bounds some3 none)),
      ("vc6.opb", "vc6_bounds_ub_above", some (Claim.bounds some3 (some 5))), -- VeriPB rejects (ub ≠ best)
      ("vc6.opb", "vc6_solval_ok", some (Claim.bounds some3 some3)),     -- soli ... : 3
      ("vc6.opb", "vc6_sat_obj", some Claim.sat),                       -- VeriPB rejects (objective)
      ("vc6.opb", "vc6_lb_too_high", none),       -- lb 4 above the best value 3
      ("vc6.opb", "vc6_lb_not_implied", none),    -- hint 1 does not imply obj ≥ 3 (VeriPB accepts:
                                                  -- it ignores the hint when the db has a contradiction)
      ("vc6.opb", "vc6_lb_nohint", none),         -- no hint (VeriPB accepts, CakePB cannot parse)
      ("vc6.opb", "vc6_ub_low", none),            -- ub 2 below the logged best 3
      ("vc6.opb", "vc6_ub_lits_low", none),       -- ub 2 below the value 3 of the listed solution
      ("vc6.opb", "vc6_ub_lits_bad", none),       -- the listed solution violates x1 + x2 >= 1
      -- php21_obj.opb (unsatisfiable, min: 2 x1 - x2, offset -1)
      ("php21_obj.opb", "php21_obj_inf", some (Claim.bounds none none)),
      ("php21_obj.opb", "php21_obj_lb", some (Claim.bounds (some 5) none)), -- vacuous lower bound
      ("php21_obj.opb", "php21_obj_inf_ub", none),  -- INF lower bound with a finite upper bound
      ("php21_obj.opb", "php21_obj_lb_ub", none),   -- finite ub without any solution
      -- off3.opb (min: -2 x1 -2 x2 -2 x3 = 2 ~x1 + 2 ~x2 + 2 ~x3 - 6, optimum -2)
      ("concl/off3.opb", "off3_ok", some (Claim.bounds (some (-2)) (some (-2)))),
      ("concl/off3.opb", "off3_lb_high", none),     -- lb -1 above the best value -2
      ("concl/off3.opb", "off3_ub_low", none),      -- ub -3 below the best value -2
      ("concl/off3.opb", "off3_ub_lits_nooffset", none), -- ub -6 = value without the offset
      -- sat3.opb (decision instance)
      ("concl/sat3.opb", "sat3_hint", some Claim.sat),
      ("concl/sat3.opb", "sat3_sol", some Claim.sat),
      ("concl/sat3.opb", "sat3_bad", none),         -- the listed assignment is no solution
      ("concl/sat3.opb", "sat3_nosol", none),       -- no solution listed or logged
      -- obji3.opb (= objective_improving: min: -2 x1 -2 x2 -2 x3, optimum -2):
      -- `obji -2` gives the lower bound; without a witnessed solution no
      -- upper bound, no SAT and no UNSAT (both references agree)
      ("concl/obji3.opb", "obji3_lb", some (Claim.bounds (some (-2)) none)),
      ("concl/obji3.opb", "obji3_lb_wit", some (Claim.bounds (some (-2)) (some (-2)))),
      ("concl/obji3.opb", "obji3_ub_nowit", none),
      ("concl/obji3.opb", "obji3_unsat", none),
      ("concl/obji3.opb", "obji3_sat_nowit", none),
      ("concl/obji3.opb", "obji3_lb_inf", none),
      -- after a plain `delc` (checked deletion off) a logged solution is no
      -- witness: SAT and a finite upper bound need the explicit solution
      -- (VeriPB and CakePB agree)
      ("concl/sat3.opb", "sat3_sol_after_delc", none),
      ("concl/sat3.opb", "sat3_sol_after_delc_wit", some Claim.sat),
      ("vc6.opb", "vc6_ub_after_delc", none),
      ("vc6.opb", "vc6_ub_after_delc_wit", some (Claim.bounds (some 3) (some 3))),
      -- ou3.opb (= objective_update_subproof): `eobj` after `obju`
      ("concl/ou3.opb", "ou3_eobj_ok", some (Claim.bounds (some 2) (some 2))),
      -- nobj3.opb (decision instance): `sol`, also with the value 0 (CakePB;
      -- VeriPB rejects a value without objective)
      ("concl/nobj3.opb", "nobj3_sol", some Claim.sat),
      ("concl/nobj3.opb", "nobj3_solval", some Claim.sat)] do
    runExpect n (d ++ o) (cd ++ n ++ ".pbp") c
  -- `obju`/`eobj` rejections (CakePB rejects all; VeriPB accepts the first
  -- and the third by autoproving the goals): no subproof, `qed : id` on the
  -- subproof, a non-trivial goal without proofgoal, a wrong new objective,
  -- `eobj` mismatch, a non-core premise in the subproof; `obji`/`eobj`
  -- without objective
  for (o, n, k) in [("concl/ou3.opb", "ou3_obju_nosub", 8),
      ("concl/ou3.opb", "ou3_obju_qedid", 8), ("concl/ou3.opb", "ou3_obju_missing2", 8),
      ("concl/ou3.opb", "ou3_obju_wrongobj", 8), ("concl/ou3.opb", "ou3_eobj_bad", 9),
      ("concl/ou3.opb", "ou3_obju_noncore", 7), ("concl/nobj3.opb", "nobj3_obji", 1),
      ("concl/nobj3.opb", "nobj3_eobj", 1),
      -- `deld` of a constraint derived inside the core-only subproof
      ("concl/ou3.opb", "ou3_obju_deld", 8)] do
    runOne n (d ++ o) (cd ++ n ++ ".pbp") (expectReject := some k)
  -- a wrong value after a logged solution is rejected at the soli step
  for (o, n) in [("vc6.opb", "vc6_solval_bad"),        -- soli ... : 4 (value 3)
      ("concl/off3.opb", "off3_solval_nooffset"),          -- soli ... : 4 (objVal 4, value -2)
      ("concl/off3.opb", "off3_solval_wrong")] do          -- soli ... : -1
    runOne n (d ++ o) (cd ++ n ++ ".pbp") (expectReject := some 2)
  -- conclusion UNSAT and BOUNDS INF after a logged solution: rejected (VeriPB
  -- and CakePB too); UNSAT on an instance with an objective (VeriPB rejects,
  -- CakePB accepts)
  runExpect "vc6_fakeunsat" (d ++ "vc6.opb") (d ++ "vc6_fakeunsat_kernel.pbp") none
  runExpect "vc6_inf_after_soli" (d ++ "vc6.opb") (cd ++ "vc6_inf_after_soli.pbp") none
  -- an empty hint `: ;` is the all-false assignment (CakePB; VeriPB: no
  -- hint): no solution of sat3 / vc6 (rejected, CakePB too), a solution of
  -- allfalse (accepted, CakePB too; VeriPB rejects)
  runExpect "sat3_empty_hint" (cd ++ "sat3.opb") (cd ++ "sat3_empty_hint.pbp") none
  runExpect "vc6_ub_empty_hint" (d ++ "vc6.opb") (cd ++ "vc6_ub_empty_hint.pbp") none
  runExpect "allfalse_empty_hint" (cd ++ "allfalse.opb") (cd ++ "allfalse_empty_hint.pbp")
    (some Claim.sat)
  -- footer placement (rejected by VeriPB and CakePB): every step is
  -- accepted, the conclusion is not
  for n in ["php21_concl_before_output", "php21_concl_no_output", "php21_concl_twice",
      "php21_concl_not_last"] do
    runExpect n (d ++ "php21.opb") (cd ++ n ++ ".pbp") none
  runExpect "sat3_concl_before_output" (cd ++ "sat3.opb")
    (cd ++ "sat3_concl_before_output.pbp") none
  runExpect "php21_obj_unsat" (d ++ "php21_obj.opb") (d ++ "php21_kernel.pbp")
    (some Claim.unsat)

-- interactions of the dominance statements (Tests/data/inter, design §7 B4;
-- notes testcampaign/p3/tests2/NOTES.md). Verdicts of VeriPB 3.0.1 / CakePB
-- in the comments; PBLean agrees with CakePB everywhere except c1_red and
-- c1_dom (PARITY C1, accept side) and goalid_01_dom, goalid_02_red (PARITY B3,
-- reject side). lex2 is the 2-bit lex order of Tests/data/dom, lex1 the 1-bit one.
open PBCatcher.Tests.Differential PBCatcher.Reflect in
#eval show IO Unit from do
  let it := "PBCatcher/Tests/data/inter/"
  -- (a) soli / obji / sol between doms (lex2 on x1 x3); the soli/obji
  -- constraint is core and gets a core goal in the next dom
  for (o, n, c) in [("wobj4", "soli_dom", Claim.bounds (some 2) (some 2)),  -- core goal 7 proved
      ("wobj4", "obji_dom", Claim.bounds (some 2) (some 2)),  -- obji 2 instead of soli
      ("wobj4", "sol_dom", Claim.bounds (some 2) (some 2)),   -- sol: no constraint, no core goal
      ("wobj6", "soli_dom_obj", Claim.bounds (some 2) (some 5)),  -- objective goal #3 needs
                                                -- the soli constraint 7 (x6 -> x5)
      ("wobj6", "obji_dom_obj", Claim.bounds (some 2) (some 5)),  -- the same after obji 5
      ("wobj4", "goalid_07_dom", Claim.bounds (some 2) (some 2))] do  -- (f) soli_dom with the
                                                -- core goal written `07` (VeriPB rejects the
                                                -- leading zero at parse time, CakePB accepts)
    runExpect n (it ++ o ++ ".opb") (it ++ n ++ ".pbp") (some c)
  -- accepted by both references unless noted
  for (o, n) in [("sym4", "redef_loaded"),     -- (b) def_order lex2 (1-ary) while the 2-ary lex2
                                                -- is loaded: the next dom still uses the loaded
                                                -- definition; then load_order lex2 x3 (new) and a dom
      ("sym4", "load_dup_ok"),                  -- (c) load_order lex2 x1 x1
      ("sym4", "load_comp_ok"),                 -- (c) load_order lex2 x1 ~x1 (key x1 + 1)
      ("sym4", "load_comprev_ok"),              -- (c) load_order lex2 ~x1 x1 (key 2 - x1)
      ("delc2", "copy_delc_dom"),               -- (d) derived copy 3 of core c2, checked delc 2
                                                -- with order goal, dom whose core goal equals copy 3
      ("c1red5", "c1_red"),                     -- (e) PARITY C1: goal 2 discharged by the proved
                                                -- goal 1 whose goal CakePB drops (c1 is a
                                                -- contradiction); CakePB rejects, VeriPB accepts
      ("c1red5", "c1_red_goal2"),               -- twin: goal 2 proved itself
      ("c1red5", "c1_dom"),                     -- (e) C1 for a dom core goal (CakePB rejects)
      ("c1red5", "c1_dom_goal2"),               -- twin
      ("sym4", "goalid_02_strict"),             -- (f) strict goal written `#02` (numeric match;
                                                -- VeriPB rejects at parse time)
      ("ou5", "obju_dom"),                      -- (g) obju, then a dom whose objective goal
                                                -- #3 for the NEW objective is implied by ¬C
      ("sym4", "s2c_twodom_on_nodel"),          -- (h) dom, s2c on, dom
      ("sym4", "s2c_twodom_off"),               -- (h) dom, on, off, dom, deld of its result
      ("sym4", "dom_untouched_unsat"),          -- (i) witness untouches the order, ¬C contradicts
                                                -- the database: qed : id
      ("aux3", "red_two_leq"),                  -- (j) red under leaux, two scope leq blocks
      ("aux3", "red_two_leq_b")] do             -- (j) the second block uses its own premise
    runOne n (it ++ o ++ ".opb") (it ++ n ++ ".pbp")
  for (o, n, k) in [("wobj4", "soli_dom_nogoal", 5),  -- (a) core goal of the soli constraint
                                                -- missing (CakePB rejects, VeriPB autoproves)
      ("wobj6", "soli_dom_obj_bad", 5),         -- (a) objective goal proof without the soli
                                                -- constraint (both reject)
      ("wobj6", "soli_dom_obj_nogoal", 5),      -- (a) objective goal missing (CakePB rejects,
                                                -- VeriPB autoproves)
      ("sym4", "redef_loaded_arity", 6),        -- (b) reload with the old arity (both reject)
      ("sym4", "redef_loaded_derived", 6),      -- (b) load_order moved the first dom's result to
                                                -- the core; its goal fails (both reject)
      ("sym4", "load_dup_bad", 3),              -- (c) key increases (both reject)
      ("sym4", "load_comp_bad", 3),             -- (c) (both reject)
      ("sym4", "load_comprev_bad", 3),          -- (c) (both reject)
      ("delc2", "copy_delc_deld_dom", 6),       -- (d) copy deleted: core goal 1 uncovered (both)
      ("delc2", "copy_delc_dom_nocopy", 4),     -- (d) no copy (both reject)
      ("one1", "delc_copy_unsound", 4),         -- (d) delc of core x1 >= 1 with a derived copy and
                                                -- the empty witness; would lead to UNSAT of a
                                                -- satisfiable formula (both reject)
      ("one1", "delc_copy_ref", 4),             -- (d) the delc goal proved from the derived copy
                                                -- (core-only subproof; both reject)
      ("sym4", "goalid_01_dom", 3),             -- (f) order goal written `#01`: PARITY B3
                                                -- (CakePB accepts, VeriPB rejects at parse time)
      ("red3", "goalid_02_red", 3),             -- (f) red order goal written `#02`: PARITY B3
      ("ou5", "obju_dom_noobju", 4),            -- (g) the OLD objective's goal #3 needs a proof
                                                -- (CakePB rejects, VeriPB autoproves)
      ("sym4", "s2c_twodom_on", 6),             -- (h) deld of the second dom's result under s2c
                                                -- (both reject)
      ("sym4", "s2c_twodom_off_deld8", 7),      -- (h) deld of the first dom's result, moved to
                                                -- the core by `on` (CakePB rejects, VeriPB accepts)
      ("sym4", "dom_untouched_strict", 3),      -- (i) strict goal impossible (both reject)
      ("sym4", "dom_untouched_nostrict", 3),    -- (i) strict goal missing (both reject)
      ("sym4", "dom_untouched_unsat_goal", 3),  -- (i) contradiction only inside proofgoal #2:
                                                -- core goal 1 uncovered (CakePB rejects, VeriPB
                                                -- autoproves)
      ("aux3", "red_two_leq_stale", 3)] do      -- (j) premise of the first scope block used in
                                                -- the second (both reject)
    runOne n (it ++ o ++ ".opb") (it ++ n ++ ".pbp") (expectReject := some k)

-- repeated witness entries (Tests/data/wit, found by the P3 mutation campaign):
-- a repeated entry with the same target is accepted (VeriPB and CakePB accept),
-- a conflicting one is rejected (CakePB rejects, VeriPB keeps the first entry)
open PBCatcher.Tests.Differential PBCatcher.Reflect in
#eval show IO Unit from do
  let w := "PBCatcher/Tests/data/wit/"
  runOne "dupwit_red" (w ++ "dupwit.opb") (w ++ "dupwit_red.pbp")
  runOne "dupwit_red_twin" (w ++ "dupwit.opb") (w ++ "dupwit_red_twin.pbp")
  runOne "dupwit_red_conflict" (w ++ "dupwit.opb") (w ++ "dupwit_red_conflict.pbp")
    (expectReject := some 1)
