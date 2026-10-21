/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.Reflect

/-!
# Parser test: VeriPB 3 kernel format

Parses OPB instances of the VeriPB test suite together with the kernel
proofs that `veripb --elaborate` (VeriPB 3.0.1) writes for them
(`Tests/data/v3/`), and checks that every proof parses and contains the
statements it was selected for (`variable_form_division`,
`normalized_mir_cut` and `variable_form_mir_cut` for the `pol` operations
`c`, `n` and `m`). Apart from the last test, only parsing is tested here; which
statements the checkers accept is tested elsewhere. Further tests pin exact
OPB constraint values and check that malformed OPB and proof input is
rejected. The last test runs
`veripb_reflect` on a small instance with named (non-`x<N>`) variables, so
that the name table reaches the proof parser (`parseOPBNamed` →
`checkProofBool`).
-/

namespace VeriPB.Tests.ParseV3

open VeriPB

/-- Statement kinds occurring in a step, including nested subproof items. -/
partial def kinds (s : ProofStep) : List String :=
  let sub (sp : Option (Array ProofStep × Option Nat)) : List String :=
    match sp with
    | some (items, _) => items.toList.flatMap kinds
    | none => []
  match s with
  | .formulaSize _ => ["f"]
  | .pol ops =>
    "pol" :: ops.filterMap fun o => match o with
      | .lowerRhs => some "pol-"
      | .divVar => some "pol c"
      | .mir => some "pol n"
      | .mirVar => some "pol m"
      | _ => none
  | .rup .. => ["rup"]
  | .ia .. => ["ia"]
  | .deld _ => ["deld"]
  | .delc _ => ["delc"]
  | .delcChecked _ _ sp => "delcChecked" :: sub sp
  | .core _ => ["core"]
  | .coreRange .. => ["coreRange"]
  | .strengtheningToCore _ => ["strengthening_to_core"]
  | .pbc _ steps _ => "pbc" :: steps.toList.flatMap kinds
  | .red _ _ goals =>
    "red" :: goals.toList.flatMap fun (_, st, _) => st.toList.flatMap kinds
  | .dom _ _ goals =>
    "dom" :: goals.toList.flatMap fun (_, st, _) => st.toList.flatMap kinds
  | .strengthening r _ _ items _ =>
    (match r with | .red => "redGeneral" | .dom => "domGeneral") ::
      items.toList.flatMap kinds
  | .proofgoal _ steps _ => "proofgoal" :: steps.toList.flatMap kinds
  | .scope _ items => "scope" :: items.toList.flatMap kinds
  | .defOrder o =>
    "def_order" :: ((o.spec.getD #[]).toList.flatMap kinds ++
      (match o.transitivity with | some t => t.proof.toList.flatMap kinds | none => []) ++
      (o.reflexivity.getD #[]).toList.flatMap kinds)
  | .loadOrder .. => ["load_order"]
  | .sol _ v => [if v.isSome then "sol:val" else "sol"]
  | .soli _ v => [if v.isSome then "soli:val" else "soli"]
  | .obji _ => ["obji"]
  | .eobj _ => ["eobj"]
  | .obju k _ sp => (match k with | .new => "obju new" | .diff => "obju diff") :: sub sp
  | .output => ["output NONE"]
  | .outputClaim .. => ["output claim"]
  | .conclusion _ => ["conclusion UNSAT"]
  | .conclusionSat l => [if l.isSome then "conclusion SAT:lits" else "conclusion SAT"]
  | .conclusionBounds lb _ ub _ =>
    ["conclusion BOUNDS"] ++ (if lb == .inf || ub == .inf then ["BOUNDS INF"] else []) ++
      (match lb with | .finite a => if a < 0 then ["BOUNDS neg"] else [] | .inf => [])
  | .conclusionNone => ["conclusion NONE"]

def dataDir : String := "VeriPB/Tactic/Sat/Tests/data/v3/"

/-- Parse `name.opb` and `name_kernel.pbp`; return the instance and the proof. -/
def load (name : String) : IO (OPBInstance × Except String VeriPBProof) := do
  let opb ← IO.FS.readFile (dataDir ++ name ++ ".opb")
  let prf ← IO.FS.readFile (dataDir ++ name ++ "_kernel.pbp")
  match parseOPBNamed opb with
  | .error e => throw (IO.userError s!"{name}: OPB parse error: {e}")
  | .ok inst =>
    return (inst, parseVeriPBProofWith (VarTable.ofList inst.names inst.numVars) prf)

/-- The proof must parse and contain every statement kind in `expected`. -/
def expectParse (name : String) (expected : List String) : IO Unit := do
  let (_, r) ← load name
  match r with
  | .error e => throw (IO.userError s!"{name}: proof parse error: {e}")
  | .ok p =>
    let ks := p.steps.toList.flatMap kinds
    for k in expected do
      if !ks.contains k then
        throw (IO.userError s!"{name}: expected statement '{k}' not found in {ks.eraseDups}")
    IO.println s!"{name}: {p.steps.size} steps parsed"

/-- The constraints must be exactly `expected` (terms and degree). -/
def expectConstrs (name : String) (cs : Array Sat.PB.Constr)
    (expected : Array (List Sat.PB.Term × Nat)) : IO Unit := do
  let got := cs.map fun c => (c.terms, c.degree)
  if got != expected then
    throw (IO.userError s!"{name}: constraints {repr got}, expected {repr expected}")

/-- Parse a proof whose formula has only `x<N>` variables. -/
def parseProof (body : String) : Except String VeriPBProof :=
  parseVeriPBProof s!"pseudo-Boolean proof version 3.0\n{body}end pseudo-Boolean proof ;\n"

end VeriPB.Tests.ParseV3

open VeriPB VeriPB.Tests.ParseV3 in
#eval show IO Unit from do
  -- statements
  expectParse "all_diff" ["f", "output NONE"]
  expectParse "implication" ["ia"]
  expectParse "implication_contradiction_source" ["ia", "conclusion UNSAT"]
  expectParse "delete_core" ["delcChecked", "proofgoal"]
  expectParse "delete_core_subproof_rup" ["delcChecked", "rup"]
  expectParse "strengthening_to_core" ["strengthening_to_core"]
  expectParse "objective_improving" ["obji", "BOUNDS neg"]
  expectParse "objective_update_diff_check" ["eobj", "obju diff"]
  expectParse "objective_update_subproof"
    ["obju new", "proofgoal", "redGeneral", "core", "conclusion BOUNDS"]
  expectParse "dominance_with_aux_vars"
    ["def_order", "load_order", "domGeneral", "scope", "proofgoal", "conclusion NONE"]
  expectParse "dominance_simple_order" ["def_order", "load_order", "dom"]
  expectParse "decision_output" ["output claim"]
  expectParse "optimization_output_opposing_lits_objective" ["output claim", "obju new"]
  expectParse "conclusion_SAT_sol_in_proof" ["sol", "conclusion SAT"]
  expectParse "conclusion_BOUNDS_infeasible" ["BOUNDS INF"]
  expectParse "lower_rhs" ["pol-"]
  expectParse "solution_logging_optional_value" ["sol:val", "BOUNDS neg"]
  expectParse "solution_logging_max_objective" ["soli", "BOUNDS neg"]
  expectParse "solution_logging_improving_optimal_optional_value" ["soli:val"]
  expectParse "rup_objective_constant_term" ["rup"]
  expectParse "input_equality_with_id" ["f"]
  expectParse "card_propagation_assert_negative_rhs" ["soli"]
  -- `pol` division in variable form and mixed-integer rounding
  expectParse "variable_form_division" ["pol c"]
  expectParse "normalized_mir_cut" ["pol n"]
  expectParse "variable_form_mir_cut" ["pol m"]
  -- OPB details (exact constraint values, worked out by hand from the files)
  let (i, _) ← load "input_equality_with_id"
  -- `=` loads as `≥` then `≤` (VeriPB `get_constraints_from_terms`):
  -- `2 x1 +1 x2 +1 x3 = 2` and `-2 x1 -1 x2 -1 x3 = 1`
  expectConstrs "input_equality_with_id" i.constrs
    #[([(2, .pos 0), (1, .pos 1), (1, .pos 2)], 2),
      ([(2, .neg 0), (1, .neg 1), (1, .neg 2)], 2),
      ([(2, .neg 0), (1, .neg 1), (1, .neg 2)], 5),
      ([(2, .pos 0), (1, .pos 1), (1, .pos 2)], 0)]
  let (i, _) ← load "solution_logging_max_objective"
  -- `max: 2 x1 2 x2 2 x3` becomes `2 ~x1 + 2 ~x2 + 2 ~x3 - 6`
  match i.objective with
  | some o =>
    if o.terms != [(2, .neg 0), (2, .neg 1), (2, .neg 2)] || o.offset != -6 || !o.fromMax then
      throw (IO.userError s!"max objective: {repr o}")
  | none => throw (IO.userError "max objective missing")
  let (i, _) ← load "all_diff"
  -- named variables take indices 0, 1, ... (no `x<N>` in this file)
  if i.names.length != i.numVars || i.numVars == 0 then
    throw (IO.userError s!"all_diff: {i.names.length} names, {i.numVars} variables")
  let (i, _) ← load "normalized_mir_cut"
  -- `1 ~x1 2 x2 2 ~x3 3 x4 <= 3` becomes `1 x1 2 ~x2 2 x3 3 ~x4 >= 5`
  expectConstrs "normalized_mir_cut" i.constrs
    #[([(1, .neg 0), (2, .pos 1), (3, .neg 2), (4, .pos 3)], 5),
      ([(1, .pos 0), (2, .neg 1), (2, .pos 2), (3, .neg 3)], 5),
      ([(1, .neg 0), (1, .pos 1), (1, .pos 2)], 1),
      ([(1, .neg 0), (1, .pos 1), (1, .pos 2), (1, .pos 4)], 3)]
  let (i, _) ← load "rup_objective_constant_term"
  if (i.objective.map (·.offset)) != some 5 then
    throw (IO.userError "rup_objective_constant_term: objective constant lost")
  -- negative and zero degrees: `>= -3` clamps to `>= 0`; `-1 x1 >= -5`
  -- becomes `1 ~x1 >= -4`, clamped; `+1 x1 +1 x2 <= 2` becomes
  -- `1 ~x1 1 ~x2 >= 0`
  match parseOPBNamed "+1 x1 +1 x2 >= -3 ;\n-1 x1 >= -5 ;\n+1 x1 +1 x2 <= 2 ;\n" with
  | .error e => throw (IO.userError s!"negative degree: {e}")
  | .ok i =>
    expectConstrs "negative degree" i.constrs
      #[([(1, .pos 0), (1, .pos 1)], 0), ([(1, .neg 0)], 0),
        ([(1, .neg 0), (1, .neg 1)], 0)]
  -- malformed OPB input is rejected
  for (what, src) in [
      ("glued relation", "+1 x1>=1 +1 x2 >= 1 ;"),
      ("digit separator", "1_0 x1 >= 1 ;"),
      ("double sign", "+-3 x1 >= 1 ;"),
      ("two statements on one line", "+1 x1 >= 1 ; +1 x2 >= 1 ;"),
      ("statement over two lines", "+1 x1\n >= 1 ;"),
      ("split objective keyword", "min : +1 x1 ;\n+1 x1 >= 1 ;"),
      ("one-character variable", "+1 a >= 1 ;"),
      ("missing ';'", "+1 x1 >= 1")] do
    match parseOPBNamed src with
    | .ok i => throw (IO.userError s!"OPB {what}: accepted ({i.constrs.size} constraints)")
    | .error _ => pure ()
  IO.println "OPB checks passed"

open VeriPB VeriPB.Tests.ParseV3 in
#eval show IO Unit from do
  -- `conclusion SAT : ;` and `BOUNDS ... ub : ;` carry no hint
  -- (parser.rs `conclusion_sat`, `conclusion_bounds`)
  match parseProof "conclusion SAT : ;\n" with
  | .ok p =>
    match p.steps.toList with
    | [.conclusionSat none] => pure ()
    | _ => throw (IO.userError "conclusion SAT : ; not parsed as SAT without hint")
  | .error e => throw (IO.userError s!"conclusion SAT : ;: {e}")
  match parseProof "conclusion BOUNDS 3 5 : ;\n" with
  | .ok p =>
    match p.steps.toList with
    | [.conclusionBounds (.finite 3) none (.finite 5) none] => pure ()
    | _ => throw (IO.userError "conclusion BOUNDS 3 5 : ; not parsed without hint")
  | .error e => throw (IO.userError s!"conclusion BOUNDS 3 5 : ;: {e}")
  -- a solution hint is kept
  match parseProof "conclusion SAT : x1 ~x2 ;\n" with
  | .ok p =>
    match p.steps.toList with
    | [.conclusionSat (some [.pos "x1", .neg "x2"])] => pure ()
    | _ => throw (IO.userError "conclusion SAT hint lost")
  | .error e => throw (IO.userError s!"conclusion SAT : x1 ~x2 ;: {e}")
  -- variable indices are bounded by the token count (13 tokens here)
  match parseProof "sol x10 aa bb ;\n" with
  | .ok p =>
    if p.numVars != 12 then throw (IO.userError s!"sol x10 aa bb: {p.numVars} variables")
  | .error e => throw (IO.userError s!"sol x10 aa bb: {e}")
  -- malformed proofs are rejected
  for (what, body) in [
      ("huge variable index", "pol 1 x99999999999 + ;\n"),
      -- 12 tokens: `x12` (index 11) fits, the fresh `aa` would get index 12
      ("fresh name beyond the bound", "sol x12 aa ;\n"),
      ("digit separator in an ID", "pol 1_0 1 + ;\n"),
      ("digit separator in a rup hint", "rup 1 x1 >= 1 : 1_0 ;\n"),
      ("double sign", "rup +-3 x1 >= 1 : ;\n")] do
    match parseProof body with
    | .ok _ => throw (IO.userError s!"proof {what}: accepted")
    | .error _ => pure ()
  IO.println "parser strictness checks passed"

namespace VeriPB.Tests.ParseV3

-- Named variables `ab`, `cd` (indices 0, 1) in both the OPB and the proof.
veripb_reflect named_vars_reflect
  "VeriPB/Tactic/Sat/Tests/data/named_vars.opb"
  "VeriPB/Tactic/Sat/Tests/data/named_vars_kernel.pbp"

end VeriPB.Tests.ParseV3
