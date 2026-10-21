/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.Reflect

/-!
# Fast checker differential test

`VeriPB.Reflect.checkProofBool` (verified, List-based) is replaced at
runtime by `VeriPB.Reflect.Fast.checkProofBoolFast` via `@[implemented_by]`.
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

namespace VeriPB.Tests.Differential

open VeriPB.Reflect

def constrEq (a b : Constr) : Bool :=
  a.degree == b.degree && a.terms.length == b.terms.length &&
    (a.terms.zip b.terms).all fun ((c1, l1), (c2, l2)) => c1 == c2 && l1 == l2

def showConstr (c : Constr) : String :=
  let ts := c.terms.map fun (a, l) => match l with
    | .pos v => s!"{a}·x{v}"
    | .neg v => s!"{a}·~x{v}"
  s!"{ts} ≥ {c.degree}"

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
  let inst ← match VeriPB.parseOPBNamed opbStr with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{name}: OPB parse error: {e}")
  let obj : Objective := match inst.objective with
    | some o => o.terms
    | none => []
  let offset : Int := match inst.objective with
    | some o => o.offset
    | none => 0
  let proof ← match VeriPB.parseVeriPBProofWith
      (VeriPB.VarTable.ofList inst.names inst.numVars) proofStr with
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
      if s.best != f.best || s.offset != f.offset then
        throw (IO.userError s!"{name}: MISMATCH at step {k}: best {s.best} vs {f.best}")
      if s.s2c != f.s2c || sortedIds s.coreIds != sortedIds f.coreIds then
        throw (IO.userError s!"{name}: MISMATCH at step {k}: core sets \
          {sortedIds s.coreIds} vs {sortedIds f.coreIds}")
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
  let claim? (getC : Nat → Option Constr) (best : Option Nat) : Option Claim :=
    match lastConclusion proof.steps with
    | some st => conclusionClaim getC constrs obj offset best st
    | none => none
  let cSlow := claim? (fun id => slow.db[id]?) slow.best
  let cFast := claim? (fun id => (fast.db[id]?).map Fast.fromFConstr) fast.best
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

end VeriPB.Tests.Differential

open VeriPB.Tests.Differential VeriPB.Reflect in
#eval show IO Unit from do
  let d := "VeriPB/Tactic/Sat/Tests/data/"
  for n in ["php21", "red_subproof", "red_swap", "red_const", "red_neglit", "red_basic",
      "weaken_cases", "rup_cases", "rup_prop"] do
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
  -- (CakePB cannot parse `max:`). The expected rejections are statements the
  -- checker does not support yet (output claims, loading an order, dominance, obji/eobj/obju)
  -- and strengthening_to_core with a derived constraint touched by the
  -- witness (database goals range over the whole database, see Reflect).
  let v := d ++ "v3/"
  for n in ["all_diff", "card_propagation_assert_negative_rhs",
      "conclusion_BOUNDS_infeasible", "conclusion_SAT_sol_in_proof", "delete_core",
      "delete_core_subproof_rup", "implication_contradiction_source", "implication",
      "input_equality_with_id", "lower_rhs", "rup", "rup_php65",
      "variable_form_division", "normalized_mir_cut", "variable_form_mir_cut",
      "rup_objective_constant_term",
      "solution_logging_improving_optimal_optional_value", "solution_logging_max_objective",
      "solution_logging_optional_value"] do
    runOne n (v ++ n ++ ".opb") (v ++ n ++ "_kernel.pbp")
  for (n, k) in [("decision_output", 8), ("dominance_simple_order", 2),
      ("dominance_with_aux_vars", 2), ("objective_improving", 2),
      ("objective_update_diff_check", 1), ("objective_update_subproof", 8),
      ("optimization_output_opposing_lits_objective", 8),
      ("strengthening_to_core", 3)] do
    runOne n (v ++ n ++ ".opb") (v ++ n ++ "_kernel.pbp") (expectReject := some k)
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
      ("concl/sat3.opb", "sat3_nosol", none)] do    -- no solution listed or logged
    runExpect n (d ++ o) (cd ++ n ++ ".pbp") c
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
