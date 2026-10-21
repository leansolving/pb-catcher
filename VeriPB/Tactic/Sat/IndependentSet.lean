/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import Lean
import Std
import VeriPB.Tactic.Sat.PseudoBoolean
import VeriPB.Tactic.Sat.FromVeriPB
import VeriPB.Tactic.Sat.Reflect

/-!
# Trusted Independent Set Encoding

End-to-end verified independent set: Lean defines a graph, encodes the independent
set decision problem as PB constraints, verifies a VeriPB kernel proof, and produces
a mathematical theorem about the maximum independent set size.

## Main definitions

* `IndependentSet.Graph` — a graph as vertex count + edge list
* `IndependentSet.encode` — encode as PB constraints (edge + cardinality)
* `IndependentSet.hasIndependentSet` — mathematical predicate
* `IndependentSet.no_large_indset_of_unsat` — encoding soundness
* `independent_set_decide` — command that calls RoundingSat + VeriPB and verifies
-/

namespace IndependentSet

open Sat.PB

-- Graph representation

/-- A graph: number of vertices (0-indexed) and edge list. -/
structure Graph where
  numVerts : Nat
  edges : List (Nat × Nat)
  deriving Repr

-- Paley graph construction

/-- Check if a is a quadratic residue mod p. -/
def isQuadResidue (a p : Nat) : Bool :=
  if a % p == 0 then false
  else (List.range p).any fun x => (x * x) % p == a % p

/-- Construct the Paley graph on p vertices (p must be prime ≡ 1 mod 4).
    Vertices are 0..p-1; edge (i,j) exists iff (i-j) is a quadratic residue. -/
def paley (p : Nat) : Graph :=
  let edges := (List.range p).flatMap fun i =>
    (List.range p).filterMap fun j =>
      if i < j && isQuadResidue ((p + j - i) % p) p then some (i, j)
      else none
  ⟨p, edges⟩

-- Encoding

/-- Build edge constraints: for each edge (u,v), add `~x_u + ~x_v >= 1`.
    This ensures at most one endpoint is selected (independent set property). -/
def mkEdgeConstrs : List (Nat × Nat) → List Constr
  | [] => []
  | (u, v) :: es =>
    ⟨[(1, Literal.neg u), (1, Literal.neg v)], 1⟩ :: mkEdgeConstrs es

/-- Build cardinality constraint: `x_0 + ... + x_{n-1} >= target`.
    This ensures at least `target` vertices are selected. -/
def mkCardConstr (numVerts target : Nat) : Constr :=
  let terms := (List.range numVerts).map fun i => (1, Literal.pos i)
  ⟨terms, target⟩

/-- Encode independent set decision problem: given graph G and target k,
    the encoding is satisfiable iff G has an independent set of size ≥ k. -/
def encode (g : Graph) (target : Nat) : Array Constr :=
  let edgeConstrs := mkEdgeConstrs g.edges
  let cardConstr := mkCardConstr g.numVerts target
  (edgeConstrs ++ [cardConstr]).toArray

-- Mathematical predicate

/-- Count how many indices satisfy a predicate. -/
def countTrue (f : Nat → Bool) (n : Nat) : Nat :=
  (List.range n).filter f |>.length

/-- A Boolean function represents an independent set of G if for every edge (u,v),
    at most one endpoint is selected. -/
def isIndependentSet (g : Graph) (f : Nat → Bool) : Prop :=
  ∀ e ∈ g.edges, ¬(f e.1 ∧ f e.2)

/-- G has an independent set of size at least k. -/
def hasIndependentSet (g : Graph) (k : Nat) : Prop :=
  ∃ f : Nat → Bool, isIndependentSet g f ∧ countTrue f g.numVerts ≥ k

/-- k is the independence number of G: has IS of size k, but not k+1. -/
def independenceNumber (g : Graph) (k : Nat) : Prop :=
  hasIndependentSet g k ∧ ¬hasIndependentSet g (k + 1)

-- Encoding soundness

theorem edgeConstr_sat_implies_independent (u v : Nat) (f : Valuation)
    (h : (⟨[(1, Literal.neg u), (1, Literal.neg v)], 1⟩ : Constr).sat f) :
    ¬(f u ∧ f v) := by
  simp only [Constr.sat, evalSum, evalLit] at h
  intro ⟨hu, hv⟩
  simp [hu, hv] at h

theorem mkEdgeConstrs_sat_implies_independent (es : List (Nat × Nat)) (f : Valuation)
    (h : ∀ c ∈ mkEdgeConstrs es, c.sat f) :
    ∀ e ∈ es, ¬(f e.1 ∧ f e.2) := by
  induction es with
  | nil => intro e he; cases he
  | cons e' es ih =>
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · apply edgeConstr_sat_implies_independent
      apply h
      simp [mkEdgeConstrs]
    · apply ih
      · intro c hc
        apply h
        simp [mkEdgeConstrs, hc]
      · exact he

theorem countTrue_succ (f : Nat → Bool) (n : Nat) :
    countTrue f (n + 1) = countTrue f n + (if f n then 1 else 0) := by
  simp only [countTrue, List.range_succ, List.filter_append, List.filter,
    List.length_append]
  cases f n <;> simp

theorem evalSum_posLits (f : Valuation) (n : Nat) :
    evalSum f ((List.range n).map fun i => (1, Literal.pos i)) =
    countTrue f n := by
  induction n with
  | zero => simp [evalSum, countTrue]
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map]
    rw [evalSum_append, ih]
    simp only [evalSum, evalLit]
    rw [countTrue_succ]
    cases f n <;> simp

theorem cardConstr_sat_implies_bound (n target : Nat) (f : Valuation)
    (h : (mkCardConstr n target).sat f) :
    countTrue f n ≥ target := by
  simp only [mkCardConstr, Constr.sat] at h
  rw [evalSum_posLits] at h
  exact h

/-- Main encoding soundness: satisfying assignment implies independent set. -/
theorem encode_sat_implies_indset (g : Graph) (target : Nat) (f : Valuation)
    (h : ∀ c ∈ (encode g target).toList, c.sat f) :
    isIndependentSet g f ∧ countTrue f g.numVerts ≥ target := by
  have henc : (encode g target).toList =
      mkEdgeConstrs g.edges ++ [mkCardConstr g.numVerts target] := rfl
  rw [henc] at h
  constructor
  · apply mkEdgeConstrs_sat_implies_independent
    intro c hc
    apply h
    simp [hc]
  · apply cardConstr_sat_implies_bound
    apply h
    simp

-- Helper: edge constraint membership implies edge membership
theorem mkEdgeConstrs_mem_edges : (es : List (Nat × Nat)) → (c : Constr) →
    c ∈ mkEdgeConstrs es → ∃ u v, (u, v) ∈ es ∧
      c = ⟨[(1, Literal.neg u), (1, Literal.neg v)], 1⟩
  | [], _, hc => by cases hc
  | (eu, ev) :: es, c, hc => by
    simp only [mkEdgeConstrs, List.mem_cons] at hc
    rcases hc with rfl | hc
    · refine ⟨eu, ev, ?_, rfl⟩; simp
    · obtain ⟨u, v, he, hceq⟩ := mkEdgeConstrs_mem_edges es c hc
      refine ⟨u, v, ?_, hceq⟩; simp [he]

/-- If the encoding is unsatisfiable, no independent set of that size exists. -/
theorem no_large_indset_of_unsat (g : Graph) (target : Nat)
    (hunsat : ∀ v : Valuation, ∃ c ∈ (encode g target).toList, ¬c.sat v) :
    ¬hasIndependentSet g target := by
  intro ⟨f, hindep, hcount⟩
  obtain ⟨c, hc, hnsat⟩ := hunsat f
  have henc : (encode g target).toList =
      mkEdgeConstrs g.edges ++ [mkCardConstr g.numVerts target] := rfl
  rw [henc] at hc
  simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · -- c is an edge constraint
    have hmem := mkEdgeConstrs_mem_edges g.edges c hc
    obtain ⟨u, v, he, hceq⟩ := hmem
    rw [hceq] at hnsat
    apply hnsat
    simp only [Constr.sat, evalSum, evalLit]
    have := hindep (u, v) he
    -- At most one of f u, f v is true
    cases hu : f u <;> cases hv : f v <;> simp_all
  · -- c is the cardinality constraint
    apply hnsat
    simp only [mkCardConstr, Constr.sat]
    rw [evalSum_posLits]
    exact hcount

-- Bridge theorem for connecting PB refutation to mathematical statement

private theorem exists_not_sat_of_allSat_false (ctx : PBFmla) (v : Valuation)
    (h : PBFmla.allSat v ctx → False) : ∃ c ∈ ctx, ¬c.sat v :=
  Classical.byContradiction fun hne =>
    h ⟨fun c hc => Classical.byContradiction fun hnsat => hne ⟨c, hc, hnsat⟩⟩

/-- Bridge from PBFmla refutation to independent set non-existence.
    Given a PB-level refutation of the encoding, derive the mathematical
    theorem. The `ctx` must be the encoding of the independent set problem. -/
theorem bridge (g : Graph) (target : Nat) (ctx : PBFmla)
    (hctx : ctx = (encode g target).toList)
    (hunsat : ∀ v : Valuation, PBFmla.allSat v ctx → False) :
    ¬hasIndependentSet g target := by
  apply no_large_indset_of_unsat g target
  intro v
  rw [← hctx]
  exact exists_not_sat_of_allSat_false ctx v (hunsat v)

-- OPB generation

/-- Generate OPB format string for the encoded constraints. -/
def toOPB (g : Graph) (target : Nat) : String := Id.run do
  let n := g.numVerts
  let numConstrs := g.edges.length + 1
  let mut s := s!"* #variable= {n} #constraint= {numConstrs} #equal= 0 intsize= 6\n"
  -- Edge constraints: ~x_u + ~x_v >= 1
  for (u, v) in g.edges do
    s := s ++ s!"+1 ~x{u+1} +1 ~x{v+1} >= 1 ;\n"
  -- Cardinality constraint: x_0 + ... + x_{n-1} >= target
  for i in List.range n do
    s := s ++ s!"+1 x{i+1} "
  s := s ++ s!">= {target} ;\n"
  return s

-- Witness verification for upper bounds (proving IS exists)

/-- Check that a set (given as Bool function) is a valid independent set. -/
def checkIndependent (g : Graph) (f : Nat → Bool) : Bool :=
  g.edges.all fun (u, v) => !(f u && f v)

/-- Check that a set has at least k elements. -/
def checkSize (n k : Nat) (f : Nat → Bool) : Bool :=
  countTrue f n ≥ k

theorem checkIndependent_spec (g : Graph) (f : Nat → Bool) :
    checkIndependent g f = true → isIndependentSet g f := by
  intro h
  simp only [checkIndependent, List.all_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff] at h
  intro e he
  have := h e he
  intro ⟨h1, h2⟩
  simp [h1, h2] at this

theorem checkSize_spec (n k : Nat) (f : Nat → Bool) :
    checkSize n k f = true → countTrue f n ≥ k := by
  simp only [checkSize, decide_eq_true_eq, ge_iff_le]
  exact id

/-- Provide a witness for lower bound: f is an independent set of size ≥ k. -/
theorem witness_indset (g : Graph) (k : Nat) (f : Nat → Bool)
    (hindep : checkIndependent g f = true)
    (hsize : checkSize g.numVerts k f = true) :
    hasIndependentSet g k :=
  ⟨f, checkIndependent_spec g f hindep, checkSize_spec g.numVerts k f hsize⟩

-- Elaboration command

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

-- Run an external process in MetaM; throw on non-zero exit code.
private def runCmdMeta (cmd : String) (args : Array String)
    (errCtx : String) : MetaM String := do
  let result ← IO.Process.output {
    cmd := cmd
    args := args
  }
  if result.exitCode != 0 then
    throwError "{errCtx}: {cmd} failed (exit {result.exitCode})\
      \nstderr: {result.stderr}\nstdout: {result.stdout}"
  return result.stdout

private def extractEdgeList (e : Expr) : MetaM (List (Nat × Nat)) := do
  let mut result : List (Nat × Nat) := []
  let mut curr := e
  while true do
    -- List.cons : {α} → α → List α → List α (3 args)
    if let some (_, hdExpr, tlExpr) := curr.app3? ``List.cons then
      -- Prod.mk : {α} → {β} → α → β → α × β (4 args)
      if let some (_, _, uExpr, vExpr) := hdExpr.app4? ``Prod.mk then
        let some u := uExpr.rawNatLit? | throwError "edge vertex not a literal"
        let some v := vExpr.rawNatLit? | throwError "edge vertex not a literal"
        result := (u, v) :: result
        curr := tlExpr
      else
        throwError "edge not a Prod.mk"
    else if curr.isAppOf ``List.nil then
      break
    else
      throwError "edges not a proper list"
  return result.reverse

private def buildBridgeProof (gExpr targetExpr : Expr)
    (ctx : Expr) (pbProofConst : Expr) :
    MetaM (Expr × Expr) := do
  let finalType := mkApp (mkConst ``Not)
    (mkApp2 (mkConst ``hasIndependentSet) gExpr targetExpr)
  -- Build hctx proof: ctx = (encode g target).toList via rfl
  let hctxProof := mkApp2 (mkConst ``Eq.refl [.succ .zero])
    (mkConst ``Sat.PB.PBFmla) ctx
  -- Apply bridge theorem: bridge g target ctx hctx pbProofConst
  let finalProof := mkApp5 (mkConst ``IndependentSet.bridge)
    gExpr targetExpr ctx hctxProof pbProofConst
  return (finalType, finalProof)

-- `independent_set_decide name G target` automatically proves
-- ¬ hasIndependentSet G target by calling RoundingSat + VeriPB.
elab "independent_set_decide " n:ident ppSpace gExpr:term:max
    ppSpace targetTerm:term : command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    -- Elaborate graph and target expressions
    let gVal ← Lean.Elab.Term.elabTerm gExpr (some (mkConst ``Graph))
    let gVal ← instantiateMVars gVal
    let targetVal ← Lean.Elab.Term.elabTerm targetTerm (some (mkConst ``Nat))
    let targetVal ← instantiateMVars targetVal
    -- Fully reduce to normalize all sub-expressions
    let gReduced ← withTransparency .all
      (reduce gVal (skipTypes := false) (skipProofs := true))
    let targetReduced ← withTransparency .all
      (reduce targetVal (skipTypes := false) (skipProofs := true))
    -- Extract graph structure (Graph.mk takes 2 args: numVerts, edges)
    let some (numVertsExpr, edgesExpr) := gReduced.app2? ``Graph.mk
      | throwError "could not reduce graph to Graph.mk"
    let some numVerts := numVertsExpr.rawNatLit?
      | throwError "could not extract numVerts as literal"
    -- Extract edges list
    let edges ← extractEdgeList edgesExpr
    let some target := targetReduced.rawNatLit?
      | throwError "could not extract target as literal"
    if target > numVerts then
      throwError "target {target} exceeds vertex count {numVerts}"
    let g : Graph := ⟨numVerts, edges⟩
    -- Write OPB to temp file
    let tmpDir ← IO.Process.output { cmd := "mktemp", args := #["-d"] }
    if tmpDir.exitCode != 0 then
      throwError "mktemp failed (exit {tmpDir.exitCode}): {tmpDir.stderr}"
    let tmpPath := tmpDir.stdout.trimAscii.toString
    if tmpPath.isEmpty then throwError "mktemp returned empty path"
    let opbPath := s!"{tmpPath}/instance.opb"
    let augPath := s!"{tmpPath}/proof_aug.pbp"
    let kernelPath := s!"{tmpPath}/proof_kernel.pbp"
    let cleanup : MetaM Unit := do
      let _ ← IO.Process.output { cmd := "rm", args := #["-rf", tmpPath] }
    try
      IO.FS.writeFile (System.FilePath.mk opbPath) (toOPB g target)
      -- Call RoundingSat
      let _ ← runCmdMeta "roundingsat"
        #[opbPath, s!"--proof-log={augPath}"] "RoundingSat"
      -- Elaborate to kernel format with VeriPB
      let _ ← runCmdMeta "veripb"
        #["--elaborate", kernelPath, opbPath, augPath] "VeriPB"
    catch e =>
      cleanup
      throw e
    -- Read kernel proof
    let proofStr ← IO.FS.readFile (System.FilePath.mk kernelPath)
    cleanup
    -- Verify in Lean
    let constrs := encode g target
    let auxName := name ++ `aux
    let (ctx, _ctx', pbProofConst) ←
      VeriPB.fromVeriPBDirect constrs numVerts proofStr auxName
    -- Build the bridge proof
    let (finalType, finalProof) ←
      buildBridgeProof gVal targetVal ctx pbProofConst
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : ¬ hasIndependentSet G {target} (fully verified)"

-- Reflection-based verification (scalable, uses native_decide)
-- Proves ¬hasIndependentSet g target from a pre-computed kernel proof file.
elab "independent_set_reflect " n:ident ppSpace gExpr:term:max
    ppSpace targetTerm:num ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let proofPath := proofFile.getString
  liftTermElabM do
    let gVal ← Lean.Elab.Term.elabTerm gExpr (some (mkConst ``Graph))
    let gVal ← instantiateMVars gVal
    let target := targetTerm.getNat
    let targetVal := mkRawNatLit target
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath)
    -- Build Exprs symbolically (native_decide evaluates at compile time)
    let constrsExpr := mkApp2 (mkConst ``encode) gVal targetVal
    let numVarsExpr := mkApp (mkConst ``Graph.numVerts) gVal
    let proofStrExpr := mkStrLit proofStr
    -- checkProofBool (encode g target) numVerts proofStr
    let checkExpr := mkApp5 (mkConst ``VeriPB.Reflect.checkProofBool)
      constrsExpr numVarsExpr
      VeriPB.Reflect.emptyObjectiveExpr VeriPB.Reflect.emptyNamesExpr
      proofStrExpr
    let hEqTrue ← match ← Lean.Meta.nativeEqTrue `independent_set_reflect checkExpr
        (axiomDeclRange? := (← getRef)) with
      | .success prf => pure prf
      | .notTrue => throwError "Reflection checker returned false for {name}"
    -- checkProof_sound → formulaUnsat (encode g target)
    let unsatProof := mkApp6
      (mkConst ``VeriPB.Reflect.checkProof_sound)
      constrsExpr numVarsExpr
      VeriPB.Reflect.emptyObjectiveExpr VeriPB.Reflect.emptyNamesExpr
      proofStrExpr hEqTrue
    -- no_large_indset_of_unsat → ¬hasIndependentSet g target
    let finalProof := mkApp3 (mkConst ``no_large_indset_of_unsat)
      gVal targetVal unsatProof
    let finalType := mkApp (mkConst ``Not)
      (mkApp2 (mkConst ``hasIndependentSet) gVal targetVal)
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : ¬ hasIndependentSet (reflection)"

/-! ### Optimization form: the independence number from one proof

`min: -1 x_0 ... -1 x_{n-1}` over the edge constraints. In normalized
minimization form the objective is `Σ ¬x_i` with constant `−n`, so the OPB
value of a valuation is `−|{i | f i}|`. A VeriPB `conclusion BOUNDS −k : id
−k : solution` certifies both `α ≤ k` (every independent set has `−size ≥
−k`) and `α ≥ k` (the solution). -/

/-- Edge constraints only (no cardinality constraint). -/
def encodeOpt (g : Graph) : Array Constr := (mkEdgeConstrs g.edges).toArray

/-- The normalized objective `Σ ¬x_i` of `min: -1 x_1 ... -1 x_n` (OPB names; internal variables `0..n-1`). -/
def misObjective (g : Graph) : VeriPB.Reflect.Objective :=
  (List.range g.numVerts).map fun i => (1, Literal.neg i)

/-- Its constant: `−n`. -/
def misOffset (g : Graph) : Int := -(g.numVerts : Int)

theorem evalSum_negLits (f : Valuation) (n : Nat) :
    evalSum f ((List.range n).map fun i => (1, Literal.neg i)) + countTrue f n
      = n := by
  induction n with
  | zero => simp [evalSum, countTrue]
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map]
    rw [evalSum_append, countTrue_succ]
    simp only [evalSum, evalLit]
    cases f n <;> simp <;> omega

/-- The OPB value of `f` is minus the number of selected vertices. -/
theorem misObjective_opbVal (g : Graph) (f : Valuation) :
    VeriPB.Reflect.opbVal (misObjective g) (misOffset g) f =
      -(countTrue f g.numVerts : Int) := by
  have h := evalSum_negLits f g.numVerts
  simp only [VeriPB.Reflect.opbVal, VeriPB.Reflect.objVal, misObjective, misOffset]
  omega

theorem encodeOpt_sat_indset (g : Graph) (f : Valuation)
    (h : VeriPB.Reflect.FormulaSat (encodeOpt g) f) : isIndependentSet g f :=
  mkEdgeConstrs_sat_implies_independent g.edges f fun c hc => h c (by
    simpa [encodeOpt] using hc)

theorem indset_sat_encodeOpt (g : Graph) (f : Valuation)
    (h : isIndependentSet g f) : VeriPB.Reflect.FormulaSat (encodeOpt g) f := by
  intro c hc
  have hc' : c ∈ mkEdgeConstrs g.edges := by simpa [encodeOpt] using hc
  obtain ⟨u, v, he, hceq⟩ := mkEdgeConstrs_mem_edges g.edges c hc'
  rw [hceq]
  simp only [Constr.sat, evalSum, evalLit]
  have := h (u, v) he
  cases hu : f u <;> cases hv : f v <;> simp_all

/-- Bridge: the bounds `−k ≤ −|S| ≤ −k` over the edge constraints give the
independence number `k`. -/
theorem independenceNumber_of_bounds (g : Graph) (k : Nat)
    (h : VeriPB.Reflect.formulaBounds (encodeOpt g) (misObjective g) (misOffset g)
      (some (-(k : Int))) (some (-(k : Int)))) :
    independenceNumber g k := by
  obtain ⟨hlb, hub⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨ρ, hρ, hval⟩ := hub
    have hv : VeriPB.Reflect.opbVal (misObjective g) (misOffset g) ρ ≤ -(k : Int) :=
      hval
    rw [misObjective_opbVal] at hv
    exact ⟨ρ, encodeOpt_sat_indset g ρ hρ, by omega⟩
  · intro ⟨f, hindep, hcount⟩
    have hv := hlb f (indset_sat_encodeOpt g f hindep)
    have hv' : -(k : Int) ≤ VeriPB.Reflect.opbVal (misObjective g) (misOffset g) f :=
      hv
    rw [misObjective_opbVal] at hv'
    omega

/-- `independent_set_opt_reflect name g k "proof.pbp"`: the independence
number `k` of `g` from one VeriPB optimization proof of
`min: -1 x_1 ... -1 x_n` over the edge constraints (`conclusion BOUNDS
−k : id −k : solution`), by native evaluation of `checkProofClaimBool`. This records a per-use axiom `checkProofClaimBool ... = true` (`_native.independent_set_opt_reflect.ax_*`, the same mechanism as `native_decide`; see `mkFormulaUnsatProof`). -/
elab "independent_set_opt_reflect " n:ident ppSpace gExpr:term:max
    ppSpace kTerm:num ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let proofPath := proofFile.getString
  liftTermElabM do
    let gVal ← Lean.Elab.Term.elabTerm gExpr (some (mkConst ``Graph))
    let gVal ← instantiateMVars gVal
    let k := kTerm.getNat
    let kVal := mkRawNatLit k
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath)
    let constrsExpr := mkApp (mkConst ``encodeOpt) gVal
    let numVarsExpr := mkApp (mkConst ``Graph.numVerts) gVal
    let objExpr := mkApp (mkConst ``misObjective) gVal
    let offsetExpr := mkApp (mkConst ``misOffset) gVal
    let claim := VeriPB.Reflect.Claim.bounds (some (-(k : Int))) (some (-(k : Int)))
    let boundsProof ← VeriPB.Reflect.mkClaimProof `independent_set_opt_reflect
      constrsExpr numVarsExpr objExpr offsetExpr proofStr claim
      (ref? := some (← getRef))
    let finalProof := mkApp3 (mkConst ``independenceNumber_of_bounds) gVal kVal
      boundsProof
    let finalType := mkApp2 (mkConst ``independenceNumber) gVal kVal
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : independenceNumber G {k} (reflection)"

end IndependentSet

-- ============================================================
-- Paley graph independence numbers
-- Upper bounds via reflection checker (pre-computed OPB + kernel proofs).
-- Lower bounds via explicit witnesses checked by native_decide.
-- ============================================================

namespace PaleyShowcase

section PaleyOptions
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open IndependentSet

-- Paley(13): α = 3
independent_set_reflect paley13_no_is4 (paley 13) 4
  "applications/paley/Paley_13_kernel.pbp"
theorem paley13_has_is3 : hasIndependentSet (paley 13) 3 :=
  witness_indset (paley 13) 3 (fun | 0 | 2 | 8 => true | _ => false)
    (by native_decide) (by native_decide)
theorem paley13_alpha : independenceNumber (paley 13) 3 :=
  ⟨paley13_has_is3, paley13_no_is4⟩

-- Paley(17): α = 3
independent_set_reflect paley17_no_is4 (paley 17) 4
  "applications/paley/Paley_17_kernel.pbp"
theorem paley17_has_is3 : hasIndependentSet (paley 17) 3 :=
  witness_indset (paley 17) 3 (fun | 10 | 13 | 16 => true | _ => false)
    (by native_decide) (by native_decide)
theorem paley17_alpha : independenceNumber (paley 17) 3 :=
  ⟨paley17_has_is3, paley17_no_is4⟩

-- Paley(29): α = 4
independent_set_reflect paley29_no_is5 (paley 29) 5
  "applications/paley/Paley_29_kernel.pbp"
theorem paley29_has_is4 : hasIndependentSet (paley 29) 4 :=
  witness_indset (paley 29) 4 (fun | 1 | 12 | 15 | 27 => true | _ => false)
    (by native_decide) (by native_decide)
theorem paley29_alpha : independenceNumber (paley 29) 4 :=
  ⟨paley29_has_is4, paley29_no_is5⟩

-- Paley(37): α = 4
independent_set_reflect paley37_no_is5 (paley 37) 5
  "applications/paley/Paley_37_kernel.pbp"
theorem paley37_has_is4 : hasIndependentSet (paley 37) 4 :=
  witness_indset (paley 37) 4 (fun | 22 | 28 | 30 | 36 => true | _ => false)
    (by native_decide) (by native_decide)
theorem paley37_alpha : independenceNumber (paley 37) 4 :=
  ⟨paley37_has_is4, paley37_no_is5⟩

-- Paley(41): α = 5
independent_set_reflect paley41_no_is6 (paley 41) 6
  "applications/paley/Paley_41_kernel.pbp"
theorem paley41_has_is5 : hasIndependentSet (paley 41) 5 :=
  witness_indset (paley 41) 5 (fun | 7 | 20 | 31 | 34 | 37 => true | _ => false)
    (by native_decide) (by native_decide)
theorem paley41_alpha : independenceNumber (paley 41) 5 :=
  ⟨paley41_has_is5, paley41_no_is6⟩

-- Paley(53): α = 5
independent_set_reflect paley53_no_is6 (paley 53) 6
  "applications/paley/Paley_53_kernel.pbp"
theorem paley53_has_is5 : hasIndependentSet (paley 53) 5 :=
  witness_indset (paley 53) 5 (fun | 16 | 24 | 43 | 46 | 51 => true | _ => false)
    (by native_decide) (by native_decide)
theorem paley53_alpha : independenceNumber (paley 53) 5 :=
  ⟨paley53_has_is5, paley53_no_is6⟩

-- Paley(61): α = 5
independent_set_reflect paley61_no_is6 (paley 61) 6
  "applications/paley/Paley_61_kernel.pbp"
theorem paley61_has_is5 : hasIndependentSet (paley 61) 5 :=
  witness_indset (paley 61) 5 (fun | 1 | 9 | 33 | 39 | 41 => true | _ => false)
    (by native_decide) (by native_decide)
theorem paley61_alpha : independenceNumber (paley 61) 5 :=
  ⟨paley61_has_is5, paley61_no_is6⟩

-- Paley(73): α = 5
independent_set_reflect paley73_no_is6 (paley 73) 6
  "applications/paley/Paley_73_kernel.pbp"
theorem paley73_has_is5 : hasIndependentSet (paley 73) 5 :=
  witness_indset (paley 73) 5 (fun | 0 | 5 | 10 | 15 | 20 => true | _ => false)
    (by native_decide) (by native_decide)
theorem paley73_alpha : independenceNumber (paley 73) 5 :=
  ⟨paley73_has_is5, paley73_no_is6⟩

-- Paley(89): α = 5
independent_set_reflect paley89_no_is6 (paley 89) 6
  "applications/paley/Paley_89_kernel.pbp"
theorem paley89_has_is5 : hasIndependentSet (paley 89) 5 :=
  witness_indset (paley 89) 5 (fun | 0 | 3 | 6 | 29 | 41 => true | _ => false)
    (by native_decide) (by native_decide)
theorem paley89_alpha : independenceNumber (paley 89) 5 :=
  ⟨paley89_has_is5, paley89_no_is6⟩

-- Paley(97): α = 6
independent_set_reflect paley97_no_is7 (paley 97) 7
  "applications/paley/Paley_97_kernel.pbp"
theorem paley97_has_is6 : hasIndependentSet (paley 97) 6 :=
  witness_indset (paley 97) 6 (fun | 0 | 5 | 15 | 20 | 34 | 57 => true | _ => false)
    (by native_decide) (by native_decide)
theorem paley97_alpha : independenceNumber (paley 97) 6 :=
  ⟨paley97_has_is6, paley97_no_is7⟩

-- Paley(101): α = 5 (101 vertices, 2525 edges)
independent_set_reflect paley101_no_is6 (paley 101) 6
  "applications/paley/Paley_101_kernel.pbp"
theorem paley101_has_is5 : hasIndependentSet (paley 101) 5 :=
  witness_indset (paley 101) 5 (fun | 74 | 82 | 89 | 92 | 100 => true | _ => false)
    (by native_decide) (by native_decide)
theorem paley101_alpha : independenceNumber (paley 101) 5 :=
  ⟨paley101_has_is5, paley101_no_is6⟩

-- The independence number of Paley graphs is not monotone in p:
-- α(Paley(97)) = 6 > 5 = α(Paley(101)) despite 97 < 101.
theorem paley_alpha_not_monotone :
    ∃ p q : Nat, p < q ∧ ∃ a b : Nat,
      independenceNumber (paley p) a ∧ independenceNumber (paley q) b ∧ a > b :=
  ⟨97, 101, by omega, 6, 5, paley97_alpha, paley101_alpha, by omega⟩

end PaleyOptions

end PaleyShowcase

-- ============================================================
-- Paley graph independence numbers from single optimization proofs
-- (RoundingSat `--opt-mode=linear --lp=0`, elaborated by VeriPB; each
-- `conclusion BOUNDS -k : id -k : solution` gives both directions).
-- ============================================================

namespace PaleyOptShowcase

section PaleyOptOptions
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open IndependentSet

independent_set_opt_reflect paley13_alpha (paley 13) 3
  "applications/paley_mis/Paley_13_mis_kernel.pbp"
independent_set_opt_reflect paley17_alpha (paley 17) 3
  "applications/paley_mis/Paley_17_mis_kernel.pbp"
independent_set_opt_reflect paley29_alpha (paley 29) 4
  "applications/paley_mis/Paley_29_mis_kernel.pbp"
independent_set_opt_reflect paley37_alpha (paley 37) 4
  "applications/paley_mis/Paley_37_mis_kernel.pbp"
independent_set_opt_reflect paley41_alpha (paley 41) 5
  "applications/paley_mis/Paley_41_mis_kernel.pbp"
independent_set_opt_reflect paley53_alpha (paley 53) 5
  "applications/paley_mis/Paley_53_mis_kernel.pbp"
independent_set_opt_reflect paley61_alpha (paley 61) 5
  "applications/paley_mis/Paley_61_mis_kernel.pbp"
independent_set_opt_reflect paley73_alpha (paley 73) 5
  "applications/paley_mis/Paley_73_mis_kernel.pbp"
independent_set_opt_reflect paley89_alpha (paley 89) 5
  "applications/paley_mis/Paley_89_mis_kernel.pbp"
independent_set_opt_reflect paley97_alpha (paley 97) 6
  "applications/paley_mis/Paley_97_mis_kernel.pbp"
independent_set_opt_reflect paley101_alpha (paley 101) 5
  "applications/paley_mis/Paley_101_mis_kernel.pbp"

-- The two routes agree.
example : independenceNumber (paley 101) 5 := PaleyShowcase.paley101_alpha
example : independenceNumber (paley 101) 5 := paley101_alpha

end PaleyOptOptions

end PaleyOptShowcase

/-! ## Shared counting lemmas for the optimization bridges -/

namespace OptCount

open Sat.PB IndependentSet

theorem countTrue_le (p : Nat → Bool) (n : Nat) : countTrue p n ≤ n := by
  induction n with
  | zero => simp [countTrue]
  | succ n ih => rw [countTrue_succ]; split <;> omega

theorem countTrue_mono (p : Nat → Bool) {m n : Nat} (h : m ≤ n) :
    countTrue p m ≤ countTrue p n := by
  induction n with
  | zero => have : m = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · have := ih (by omega); rw [countTrue_succ]; omega
    · have : m = n + 1 := by omega
      subst this; exact Nat.le_refl _

/-- A position where `p` holds raises the count strictly. -/
theorem countTrue_lt_of_true (p : Nat → Bool) {a b : Nat} (ha : p a = true)
    (hab : a < b) : countTrue p a < countTrue p b := by
  have h1 : countTrue p (a + 1) = countTrue p a + 1 := by
    rw [countTrue_succ, ha]; simp
  have h2 := countTrue_mono p (show a + 1 ≤ b by omega)
  omega

/-- The rank `countTrue p a` is injective on the positions where `p` holds. -/
theorem countTrue_inj (p : Nat → Bool) {a b : Nat} (ha : p a = true)
    (hb : p b = true) (h : countTrue p a = countTrue p b) : a = b := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have := countTrue_lt_of_true p ha hlt; omega
  · exact heq
  · have := countTrue_lt_of_true p hb hgt; omega

theorem countTrue_pos_exists (p : Nat → Bool) (n : Nat) (h : 0 < countTrue p n) :
    ∃ i, i < n ∧ p i = true := by
  induction n with
  | zero => simp [countTrue] at h
  | succ n ih =>
    rw [countTrue_succ] at h
    cases hp : p n
    · rw [hp] at h
      obtain ⟨i, hi, hpi⟩ := ih (by simpa using h)
      exact ⟨i, by omega, hpi⟩
    · exact ⟨n, by omega, hp⟩

/-- The indicator of `[0, a)` counts `min a n` positions of `[0, n)`. -/
theorem countTrue_lt_const (a n : Nat) :
    countTrue (fun j => decide (j < a)) n = min a n := by
  induction n with
  | zero => simp [countTrue]
  | succ n ih =>
    rw [countTrue_succ, ih]
    rcases Nat.lt_or_ge n a with h | h
    · rw [if_pos (by simpa using h)]; omega
    · rw [if_neg (by simpa using h)]; omega

/-- The objective `Σ_{i<n} x_{b+i}` counts the true variables in the block. -/
theorem evalSum_posLits_shift (f : Valuation) (b n : Nat) :
    evalSum f ((List.range n).map fun i => (1, Literal.pos (b + i))) =
      countTrue (fun i => f (b + i)) n := by
  induction n with
  | zero => simp [evalSum, countTrue]
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map]
    rw [evalSum_append, ih, countTrue_succ]
    simp only [evalSum, evalLit]
    cases f (b + n) <;> simp

/-- Every edge joins two of the vertices `0..n-1`. -/
def edgesInRange (g : Graph) : Bool :=
  g.edges.all fun e => decide (e.1 < g.numVerts) && decide (e.2 < g.numVerts)

theorem edgesInRange_spec (g : Graph) (h : edgesInRange g = true) :
    ∀ e ∈ g.edges, e.1 < g.numVerts ∧ e.2 < g.numVerts := by
  intro e he
  simp only [edgesInRange, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h e he

end OptCount
