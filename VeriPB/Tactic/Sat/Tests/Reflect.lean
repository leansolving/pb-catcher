/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.Reflect

/-!
# Reflection-based Checker Tests

Test the reflection-based checker (`checkProofBool` + native evaluation)
on a small OPB instance with VeriPB kernel proof.
-/

namespace VeriPB.Tests.Reflect

-- PHP(2,1): 2 vars, 3 constraints. Uses rup + pol.
veripb_reflect php21_reflect
  "VeriPB/Tactic/Sat/Tests/data/php21.opb"
  "VeriPB/Tactic/Sat/Tests/data/php21_kernel.pbp"

-- Weakening semantics (VeriPB-checked proof): variable on both sides of the
-- operand, absent variable (no-op), coefficient above the degree (trivial),
-- removal from a two-block sum.
veripb_reflect weaken_cases_reflect
  "VeriPB/Tactic/Sat/Tests/data/weaken_cases.opb"
  "VeriPB/Tactic/Sat/Tests/data/weaken_cases_kernel.pbp"

-- rup semantics (VeriPB-checked proof): the target is normalized before
-- negation (complementary pair in the target), and a target with degree
-- above its coefficient sum (`rup >= 1`) is checked with the trivial
-- negation.
veripb_reflect rup_cases_reflect
  "VeriPB/Tactic/Sat/Tests/data/rup_cases.opb"
  "VeriPB/Tactic/Sat/Tests/data/rup_cases_kernel.pbp"

-- rup by unit propagation (accepted by VeriPB and CakePB): one weighted
-- constraint forces three literals at once; hints in propagation order with
-- an explicit `~` (once and twice). The rejected variants (reversed hints,
-- no `~`, no hints) are in Tests/Differential.
veripb_reflect rup_prop_reflect
  "VeriPB/Tactic/Sat/Tests/data/rup_prop.opb"
  "VeriPB/Tactic/Sat/Tests/data/rup_prop_kernel.pbp"

-- Red subproof test: pigeon-hole variant with redundance-based strengthening.
-- Uses red/dom with explicit subproof (proofgoal #1 and proofgoal 1).
-- Tests: red rule, substitution parsing, goal verification, auto-satisfaction.
-- From VeriPB test suite: redundance_explicit_subproof.
veripb_reflect red_subproof_reflect
  "VeriPB/Tactic/Sat/Tests/data/red_subproof.opb"
  "VeriPB/Tactic/Sat/Tests/data/red_subproof_kernel.pbp"

-- Red variable swap test: symmetric formula with x1↔x2 swap.
-- Tests: auto-satisfied coverage (all constraints map to each other under swap).
veripb_reflect red_swap_reflect
  "VeriPB/Tactic/Sat/Tests/data/red_swap.opb"
  "VeriPB/Tactic/Sat/Tests/data/red_swap_kernel.pbp"

-- Red with constant substitution (x1 → 0): all 4 constraints affected,
-- 3 have trivially-contra goal negates, 2 need real subproofs.
veripb_reflect red_const_reflect
  "VeriPB/Tactic/Sat/Tests/data/red_const.opb"
  "VeriPB/Tactic/Sat/Tests/data/red_const_kernel.pbp"

-- Red with negated literal substitution (x1 → ~x2, x2 → ~x1):
-- complementary swap where all constraints auto-satisfy.
veripb_reflect red_neglit_reflect
  "VeriPB/Tactic/Sat/Tests/data/red_neglit.opb"
  "VeriPB/Tactic/Sat/Tests/data/red_neglit_kernel.pbp"

-- Red with a variable swap and a `#1` goal closed by pol (formerly a `dom`
-- proof with the same content; `dom` needs an order, which CakePB requires and
-- the checker does not support yet, so `dom` is rejected).
veripb_reflect red_basic_reflect
  "VeriPB/Tactic/Sat/Tests/data/red_basic.opb"
  "VeriPB/Tactic/Sat/Tests/data/red_basic_kernel.pbp"

-- PHP(3,2): pigeonhole principle with symmetry-breaking via red rule.
-- Proof uses red to add x1≥1 (WLOG pigeon 1 goes to hole 1) with a cyclic
-- substitution (x1↔x3↔x5, x2↔x4↔x6), then derives contradiction via pol.
-- Elaborated from VeriPB test suite: redundance_explicit_subproof.
veripb_reflect php32_red_reflect
  "applications/php/php32.opb"
  "applications/php/php32_kernel.pbp"

-- UNSAT through `ia` from a contradictory source (VeriPB 3 test suite).
veripb_reflect implication_contradiction_source_reflect
  "VeriPB/Tactic/Sat/Tests/data/v3/implication_contradiction_source.opb"
  "VeriPB/Tactic/Sat/Tests/data/v3/implication_contradiction_source_kernel.pbp"

-- pol cuts from the VeriPB 3 test suite: variable-form division (`k c`),
-- normalized and variable-form mixed-integer rounding (`k n`, `k m`).
veripb_reflect variable_form_division_reflect
  "VeriPB/Tactic/Sat/Tests/data/v3/variable_form_division.opb"
  "VeriPB/Tactic/Sat/Tests/data/v3/variable_form_division_kernel.pbp"

veripb_reflect normalized_mir_cut_reflect
  "VeriPB/Tactic/Sat/Tests/data/v3/normalized_mir_cut.opb"
  "VeriPB/Tactic/Sat/Tests/data/v3/normalized_mir_cut_kernel.pbp"

veripb_reflect variable_form_mir_cut_reflect
  "VeriPB/Tactic/Sat/Tests/data/v3/variable_form_mir_cut.opb"
  "VeriPB/Tactic/Sat/Tests/data/v3/variable_form_mir_cut_kernel.pbp"

-- A constraint and the negation of one of its cuts (`3 c`, `4 n`, `3 m`;
-- Tests/data/polcut, accepted by VeriPB 3.0.1 and CakePB).
veripb_reflect polcut_unsat_c_reflect
  "VeriPB/Tactic/Sat/Tests/data/polcut/polcut_unsat_c.opb"
  "VeriPB/Tactic/Sat/Tests/data/polcut/polcut_unsat_c.pbp"

veripb_reflect polcut_unsat_n_reflect
  "VeriPB/Tactic/Sat/Tests/data/polcut/polcut_unsat_n.opb"
  "VeriPB/Tactic/Sat/Tests/data/polcut/polcut_unsat_n.pbp"

veripb_reflect polcut_unsat_m_reflect
  "VeriPB/Tactic/Sat/Tests/data/polcut/polcut_unsat_m.opb"
  "VeriPB/Tactic/Sat/Tests/data/polcut/polcut_unsat_m.pbp"

-- The same proof on the instance with an objective line (`min: +2 x1 -1 x2`):
-- `veripb_reflect` passes the parsed objective to the checker.
veripb_reflect php21_obj_reflect
  "VeriPB/Tactic/Sat/Tests/data/php21_obj.opb"
  "VeriPB/Tactic/Sat/Tests/data/php21_kernel.pbp"

/-! ## Conclusions SAT and BOUNDS

`veripb_reflect` registers a theorem matching the proof's conclusion. The
objective is the normalized min-form objective `objVal obj v + offset` (for
`max: f` the bounds are on `−f`). All accepted proofs below are accepted by
CakePB; VeriPB 3.0.1 rejects `vc6_bounds_ub_above` (ub above the best
value), `vc6_sat_obj` (SAT with an objective) and `allfalse_empty_hint`
(`conclusion SAT : ;`, no hint for VeriPB). The rejected variants are in
Tests/Differential (verified and fast checkers) and below (the command). -/

-- Minimum vertex cover of the 6-cycle with two chords: optimum 3.
veripb_reflect vc6_bounds_reflect
  "VeriPB/Tactic/Sat/Tests/data/vc6.opb"
  "VeriPB/Tactic/Sat/Tests/data/vc6_linear_kernel.pbp"

-- Optimum 3, attained: `(∃ v, FormulaSat F v ∧ objVal obj v + 0 = 3) ∧
-- ∀ v, FormulaSat F v → 3 ≤ objVal obj v + 0`.
open VeriPB.Reflect in
example := formulaBounds_optimum vc6_bounds_reflect

example := (vc6_bounds_reflect : VeriPB.Reflect.formulaBounds _ _ 0 (some 3) (some 3))

-- The same proof with `soli ... : 3`, with the upper bound from the logged
-- solution, without an upper bound, and with an upper bound above the best.
veripb_reflect vc6_solval_reflect
  "VeriPB/Tactic/Sat/Tests/data/vc6.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/vc6_solval_ok.pbp"

veripb_reflect vc6_bounds_nolits_reflect
  "VeriPB/Tactic/Sat/Tests/data/vc6.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/vc6_bounds_nolits.pbp"

veripb_reflect vc6_bounds_noub_reflect
  "VeriPB/Tactic/Sat/Tests/data/vc6.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/vc6_bounds_noub.pbp"

veripb_reflect vc6_bounds_ub_above_reflect
  "VeriPB/Tactic/Sat/Tests/data/vc6.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/vc6_bounds_ub_above.pbp"

-- `conclusion UNSAT` after a logged solution of value 3: rejected (VeriPB
-- and CakePB too), and `BOUNDS INF` on the same database likewise.
/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect vc6_fakeunsat_bad
  "VeriPB/Tactic/Sat/Tests/data/vc6.opb"
  "VeriPB/Tactic/Sat/Tests/data/vc6_fakeunsat_kernel.pbp"

/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect vc6_inf_after_soli_bad
  "VeriPB/Tactic/Sat/Tests/data/vc6.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/vc6_inf_after_soli.pbp"

-- SAT with a solution, on an instance with an objective.
veripb_reflect vc6_sat_reflect
  "VeriPB/Tactic/Sat/Tests/data/vc6.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/vc6_sat_obj.pbp"

-- Objective with offset: min: -2 x1 -2 x2 -2 x3 (terms 2 ~x1 + 2 ~x2 + 2 ~x3,
-- offset -6), optimum -2; `soli x1 ~x2 ~x3 : -2`.
veripb_reflect off3_reflect
  "VeriPB/Tactic/Sat/Tests/data/concl/off3.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/off3_ok.pbp"

example := (off3_reflect : VeriPB.Reflect.formulaBounds _ _ (-6) (some (-2)) (some (-2)))

-- Unsatisfiable instance with an objective: `BOUNDS INF : id INF` and a
-- (vacuous) finite lower bound.
veripb_reflect php21_obj_inf_reflect
  "VeriPB/Tactic/Sat/Tests/data/php21_obj.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/php21_obj_inf.pbp"

veripb_reflect php21_obj_lb_reflect
  "VeriPB/Tactic/Sat/Tests/data/php21_obj.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/php21_obj_lb.pbp"

-- SAT: a listed solution, and a logged solution.
veripb_reflect sat3_hint_reflect
  "VeriPB/Tactic/Sat/Tests/data/concl/sat3.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/sat3_hint.pbp"

veripb_reflect sat3_sol_reflect
  "VeriPB/Tactic/Sat/Tests/data/concl/sat3.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/sat3_sol.pbp"

-- `conclusion SAT : ;` is the all-false assignment (as in CakePB), here a
-- solution of `~x1 + ~x2 >= 1`.
veripb_reflect allfalse_empty_hint_reflect
  "VeriPB/Tactic/Sat/Tests/data/concl/allfalse.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/allfalse_empty_hint.pbp"

example := (allfalse_empty_hint_reflect : VeriPB.Reflect.formulaSatisfiable _)

-- VeriPB 3 test suite: BOUNDS INF, SAT after sol, bounds with offsets and a
-- max: objective (the bounds refer to its negation).
veripb_reflect conclusion_BOUNDS_infeasible_reflect
  "VeriPB/Tactic/Sat/Tests/data/v3/conclusion_BOUNDS_infeasible.opb"
  "VeriPB/Tactic/Sat/Tests/data/v3/conclusion_BOUNDS_infeasible_kernel.pbp"

example := (conclusion_BOUNDS_infeasible_reflect :
  VeriPB.Reflect.formulaBounds _ _ _ none none)

veripb_reflect conclusion_SAT_sol_in_proof_reflect
  "VeriPB/Tactic/Sat/Tests/data/v3/conclusion_SAT_sol_in_proof.opb"
  "VeriPB/Tactic/Sat/Tests/data/v3/conclusion_SAT_sol_in_proof_kernel.pbp"

veripb_reflect solution_logging_optional_value_reflect
  "VeriPB/Tactic/Sat/Tests/data/v3/solution_logging_optional_value.opb"
  "VeriPB/Tactic/Sat/Tests/data/v3/solution_logging_optional_value_kernel.pbp"

veripb_reflect solution_logging_max_objective_reflect
  "VeriPB/Tactic/Sat/Tests/data/v3/solution_logging_max_objective.opb"
  "VeriPB/Tactic/Sat/Tests/data/v3/solution_logging_max_objective_kernel.pbp"

-- `max: 2 x1 + 2 x2 + 2 x3` is `2 ~x1 + 2 ~x2 + 2 ~x3 - 6` in min form:
-- the bounds -2, -2 say that the maximum of the original objective is 2.
example := (solution_logging_max_objective_reflect :
  VeriPB.Reflect.formulaBounds _ _ (-6) (some (-2)) (some (-2)))

-- Rejected by the command (and by VeriPB and CakePB): wrong lower bound,
-- wrong upper bound, wrong solution value, finite upper bound without a
-- solution, SAT with a non-solution.
/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect vc6_lb_too_high_bad
  "VeriPB/Tactic/Sat/Tests/data/vc6.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/vc6_lb_too_high.pbp"

/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect vc6_ub_low_bad
  "VeriPB/Tactic/Sat/Tests/data/vc6.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/vc6_ub_low.pbp"

/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect vc6_solval_bad
  "VeriPB/Tactic/Sat/Tests/data/vc6.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/vc6_solval_bad.pbp"

/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect off3_solval_bad
  "VeriPB/Tactic/Sat/Tests/data/concl/off3.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/off3_solval_nooffset.pbp"

/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect php21_obj_lb_ub_bad
  "VeriPB/Tactic/Sat/Tests/data/php21_obj.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/php21_obj_lb_ub.pbp"

/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect sat3_bad
  "VeriPB/Tactic/Sat/Tests/data/concl/sat3.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/sat3_bad.pbp"

-- `conclusion SAT : ;` and an upper bound `ub : ;` read as the all-false
-- assignment, which is no solution here (CakePB rejects too; VeriPB
-- rejects the SAT proof, no solution logged, and accepts the BOUNDS proof,
-- where it uses the logged solution).
/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect sat3_empty_hint_bad
  "VeriPB/Tactic/Sat/Tests/data/concl/sat3.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/sat3_empty_hint.pbp"

/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect vc6_ub_empty_hint_bad
  "VeriPB/Tactic/Sat/Tests/data/vc6.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/vc6_ub_empty_hint.pbp"

-- Footer placement: the conclusion must be the last step, directly after
-- `output NONE`, and the only one (rejected by VeriPB and CakePB too).
/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect php21_concl_before_output_bad
  "VeriPB/Tactic/Sat/Tests/data/php21.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/php21_concl_before_output.pbp"

/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect php21_concl_no_output_bad
  "VeriPB/Tactic/Sat/Tests/data/php21.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/php21_concl_no_output.pbp"

/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect php21_concl_twice_bad
  "VeriPB/Tactic/Sat/Tests/data/php21.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/php21_concl_twice.pbp"

/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect php21_concl_not_last_bad
  "VeriPB/Tactic/Sat/Tests/data/php21.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/php21_concl_not_last.pbp"

/-- error: VeriPB reflection checker rejected the proof -/
#guard_msgs in
veripb_reflect sat3_concl_before_output_bad
  "VeriPB/Tactic/Sat/Tests/data/concl/sat3.opb"
  "VeriPB/Tactic/Sat/Tests/data/concl/sat3_concl_before_output.pbp"

/-! ## Solution logging (`soli`) and the optimization invariant

The checker runs step by step, the verified `execStepsFuel` and the fast
`Fast.execFStepsFuel` side by side; `runBoth` returns the index of the first
rejected step (it must be the same for both) or the final best value. -/

open VeriPB.Reflect in
/-- Run both step loops on an OPB file (with its objective) and a kernel
proof. Returns `.error k` if step `k` is rejected, otherwise the verified
final state; throws if the two checkers disagree. -/
def runBoth (opbPath proofPath : String) : IO (Except Nat BoolCheckState) := do
  let opbStr ← IO.FS.readFile opbPath
  let proofStr ← IO.FS.readFile proofPath
  let inst ← match VeriPB.parseOPBNamed opbStr with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"OPB parse error: {e}")
  let proof ← match VeriPB.parseVeriPBProofWith
      (VeriPB.VarTable.ofList inst.names inst.numVars) proofStr with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"proof parse error: {e}")
  let obj : Objective := match inst.objective with
    | some o => o.terms
    | none => []
  let constrs := inst.constrs
  -- the variable count of `checkProofBool` (fresh proof variables included)
  let numVars := max inst.numVars proof.numVars
  let steps := proof.steps.toList
  let fuel := pbcDepth steps + 1
  let mut st := BoolCheckState.fromConstrs constrs numVars obj
  let mut ft := Fast.FBoolCheckState.fromConstrs constrs numVars obj
  let mut k := 0
  for step in steps do
    match execStepsFuel fuel st [step], Fast.execFStepsFuel fuel ft [step] with
    | some s, some f =>
      if s.best != f.best || s.nextId != f.nextId then
        throw (IO.userError s!"{proofPath}: state differs at step {k}")
      st := s
      ft := f
    | none, none => return .error k
    | _, _ => throw (IO.userError s!"{proofPath}: acceptance differs at step {k}")
    k := k + 1
  if hasUnsatConclusion proof.steps st != Fast.hasFUnsatConclusion proof.steps ft then
    throw (IO.userError s!"{proofPath}: conclusion differs")
  return .ok st

open VeriPB.Reflect in
#eval show IO Unit from do
  let d := "VeriPB/Tactic/Sat/Tests/data/"
  -- Minimum vertex cover of a 6-cycle with two chords (optimum 3), RoundingSat
  -- linear search, elaborated by VeriPB: f, rup, soli, pol, deld, output,
  -- conclusion BOUNDS. Every step is accepted; the logged solution has
  -- value 3, `soli` allocates id 10, and id 11 is the contradiction that
  -- certifies the lower bound. `vc6_sol_soli` is the same proof with a plain
  -- `sol` of value 4 before the `soli`: `sol` adds no constraint, so the ids
  -- are unchanged, and the best value drops from 4 to 3.
  for n in ["vc6_linear", "vc6_sol_soli"] do
    match ← runBoth (d ++ "vc6.opb") (d ++ n ++ "_kernel.pbp") with
    | .error k => throw (IO.userError s!"{n}: step {k} rejected")
    | .ok s =>
      unless s.best == some 3 && s.nextId == 16 do
        throw (IO.userError s!"{n}: unexpected final state")
      unless (s.db[11]?.map fun c => c.isContra) == some true do
        throw (IO.userError s!"{n}: id 11 is not a contradiction")
  -- The logged solution violates the original constraint x1 + x2 >= 1.
  match ← runBoth (d ++ "vc6.opb") (d ++ "vc6_badsol_kernel.pbp") with
  | .error 2 => pure ()
  | _ => throw (IO.userError "vc6_badsol: soli not rejected at step 2")
  -- With a logged solution, a contradiction proves a bound, not UNSAT: every
  -- step is accepted, the UNSAT conclusion is not.
  match ← runBoth (d ++ "vc6.opb") (d ++ "vc6_fakeunsat_kernel.pbp") with
  | .ok s =>
    let proofStr ← IO.FS.readFile (d ++ "vc6_fakeunsat_kernel.pbp")
    let steps := match VeriPB.parseVeriPBProof proofStr with
      | .ok p => p.steps
      | .error _ => #[]
    if hasUnsatConclusion steps s then
      throw (IO.userError "vc6_fakeunsat: UNSAT conclusion accepted")
  | .error k => throw (IO.userError s!"vc6_fakeunsat: step {k} rejected")
  -- `vc6_fakeunsat` with `soli` replaced by a plain `sol` (value 4) and the
  -- ids after it decremented by one. The contradiction of `vc6_fakeunsat`
  -- used the improvement constraint of `soli` (id 10), which a plain `sol`
  -- does not add: the `pol` at step 3 references the missing id 10, so both
  -- checkers reject there (VeriPB too). A satisfiable formula has no sound
  -- contradiction without an improvement constraint, so this test exercises
  -- the `sol` branch, not the UNSAT guard.
  match ← runBoth (d ++ "vc6.opb") (d ++ "vc6_sol_unsat_kernel.pbp") with
  | .error 3 => pure ()
  | _ => throw (IO.userError "vc6_sol_unsat: pol on the missing id 10 not rejected at step 3")
  -- Solution logging inside a pbc subproof is rejected (positive control:
  -- the same pbc without soli, soli afterwards).
  match ← runBoth (d ++ "vc6.opb") (d ++ "vc6_pbcsol_kernel.pbp") with
  | .error 1 => pure ()
  | _ => throw (IO.userError "vc6_pbcsol: pbc with soli not rejected")
  match ← runBoth (d ++ "vc6.opb") (d ++ "vc6_pbcok_kernel.pbp") with
  | .ok s =>
    unless s.best == some 3 && s.nextId == 13 do
      throw (IO.userError "vc6_pbcok: unexpected final state")
  | .error k => throw (IO.userError s!"vc6_pbcok: step {k} rejected")
  -- A red witness that touches an objective variable needs the objective
  -- goal `#2` (x1 - x2 >= 0 here): this proof has no `proofgoal #2` and `¬C`
  -- does not imply it, so the step is rejected (CakePB too; VeriPB proves
  -- the goal by RUP because this formula is unsatisfiable). Without the
  -- objective the same proof is accepted (`red_swap_reflect` above).
  match ← runBoth (d ++ "red_swap_obj.opb") (d ++ "red_swap_kernel.pbp") with
  | .error 1 => pure ()
  | _ => throw (IO.userError "red_swap_obj: red touching the objective not rejected")
  match ← runBoth (d ++ "red_swap.opb") (d ++ "red_swap_kernel.pbp") with
  | .ok _ => pure ()
  | .error k => throw (IO.userError s!"red_swap: step {k} rejected")
  -- Solution logging inside a red proof goal is rejected. The red step adds
  -- the edge constraint x1 + x2 >= 1 with an empty witness (every vc6
  -- variable is in the objective); its goal #1 is closed by pol. Positive
  -- control: the same proof without the soli in the goal, followed by the
  -- vc6_linear derivation with ids shifted by 4 (VeriPB accepts it).
  match ← runBoth (d ++ "vc6.opb") (d ++ "vc6_redsol_kernel.pbp") with
  | .error 1 => pure ()
  | _ => throw (IO.userError "vc6_redsol: red goal with soli not rejected")
  match ← runBoth (d ++ "vc6.opb") (d ++ "vc6_redok_kernel.pbp") with
  | .ok s =>
    unless s.best == some 3 && s.nextId == 20 do
      throw (IO.userError "vc6_redok: unexpected final state")
  | .error k => throw (IO.userError s!"vc6_redok: step {k} rejected")
  IO.println "solution logging tests OK"

end VeriPB.Tests.Reflect
