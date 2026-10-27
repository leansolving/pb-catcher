/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import Lean
import Std
import PBCatcher.PseudoBoolean
import PBCatcher.Reflect
import PBCatcher.IndependentSet

/-!
# Trusted Vertex Cover Encoding (optimization form)

The vertex cover number from one VeriPB optimization proof: Lean encodes
`min: +1 x_1 ... +1 x_n` over the edge constraints `x_u + x_v ≥ 1`, the
reflection checker verifies a kernel proof ending in `conclusion BOUNDS k :
id k : solution`, and the bridge theorem turns the two bounds into the
statement that the minimum vertex cover has size `k`.

## Main definitions

* `VertexCover.encodeVC` — edge constraints `x_u + x_v ≥ 1` in edge order
* `VertexCover.vcObjective` — the objective `Σ x_i` (offset 0)
* `VertexCover.vertexCoverNumber` — mathematical predicate
* `VertexCover.vertexCoverNumber_of_bounds` — bridge theorem
* `vertex_cover_reflect` — elaboration command

The counting lemmas shared by the optimization bridges (vertex cover,
colouring, bin packing) are in `OptCount` (IndependentSet.lean).
-/


namespace VertexCover

open Sat.PB IndependentSet
open OptCount (edgesInRange edgesInRange_spec)

-- Graphs

/-- The Petersen graph: outer 5-cycle `0..4`, spokes `i – i+5`, inner
pentagram `5+i – 5+(i+2)%5`. The edges are listed as sorted pairs in
lexicographic order, the order of `applications/gen_opt_instances.py`. -/
def petersen : Graph :=
  ⟨10, [(0, 1), (0, 4), (0, 5), (1, 2), (1, 6), (2, 3), (2, 7), (3, 4), (3, 8),
        (4, 9), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9)]⟩

-- Mathematical predicates

/-- `f` covers every edge of `g` (vertices `≥ g.numVerts` are not counted by
`hasVertexCover`; the bridge theorem assumes `edgesInRange g`). -/
def isVertexCover (g : Graph) (f : Nat → Bool) : Prop :=
  ∀ e ∈ g.edges, f e.1 = true ∨ f e.2 = true

/-- `g` has a vertex cover with at most `k` of the vertices `0..n-1`. -/
def hasVertexCover (g : Graph) (k : Nat) : Prop :=
  ∃ f : Nat → Bool, isVertexCover g f ∧ countTrue f g.numVerts ≤ k

/-- `k` is the vertex cover number of `g`: some cover has size `k`, and every
cover has size at least `k`. -/
def vertexCoverNumber (g : Graph) (k : Nat) : Prop :=
  hasVertexCover g k ∧ ∀ f : Nat → Bool, isVertexCover g f → k ≤ countTrue f g.numVerts

-- Encoding

/-- Edge constraints `x_u + x_v ≥ 1`, one per edge, in edge order. -/
def mkCoverConstrs : List (Nat × Nat) → List Constr
  | [] => []
  | (u, v) :: es => ⟨[(1, Literal.pos u), (1, Literal.pos v)], 1⟩ :: mkCoverConstrs es

/-- The constraints of `min: +1 x_1 ... +1 x_n` over the edges of `g`. -/
def encodeVC (g : Graph) : Array Constr := (mkCoverConstrs g.edges).toArray

/-- The objective `Σ x_i` (offset 0). -/
def vcObjective (g : Graph) : PBCatcher.Reflect.Objective :=
  (List.range g.numVerts).map fun i => (1, Literal.pos i)

-- Encoding soundness

theorem mkCoverConstrs_mem : (es : List (Nat × Nat)) → (c : Constr) →
    c ∈ mkCoverConstrs es → ∃ u v, (u, v) ∈ es ∧
      c = ⟨[(1, Literal.pos u), (1, Literal.pos v)], 1⟩
  | [], _, hc => by cases hc
  | (eu, ev) :: es, c, hc => by
    simp only [mkCoverConstrs, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨eu, ev, by simp, rfl⟩
    · obtain ⟨u, v, he, hceq⟩ := mkCoverConstrs_mem es c hc
      exact ⟨u, v, by simp [he], hceq⟩

theorem mem_mkCoverConstrs : (es : List (Nat × Nat)) → (u v : Nat) →
    (u, v) ∈ es → (⟨[(1, Literal.pos u), (1, Literal.pos v)], 1⟩ : Constr) ∈
      mkCoverConstrs es
  | [], _, _, he => by cases he
  | (eu, ev) :: es, u, v, he => by
    simp only [List.mem_cons, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩ | he
    · simp [mkCoverConstrs]
    · simp only [mkCoverConstrs, List.mem_cons]
      exact Or.inr (mem_mkCoverConstrs es u v he)

theorem encodeVC_sat_cover (g : Graph) (f : Valuation)
    (h : PBCatcher.Reflect.FormulaSat (encodeVC g) f) : isVertexCover g f := by
  intro e he
  have hc := h _ (by simpa [encodeVC] using mem_mkCoverConstrs g.edges e.1 e.2 he)
  simp only [Constr.sat, evalSum, evalLit] at hc
  cases h1 : f e.1 <;> cases h2 : f e.2 <;> simp_all

theorem cover_sat_encodeVC (g : Graph) (f : Valuation) (h : isVertexCover g f) :
    PBCatcher.Reflect.FormulaSat (encodeVC g) f := by
  intro c hc
  have hc' : c ∈ mkCoverConstrs g.edges := by simpa [encodeVC] using hc
  obtain ⟨u, v, he, hceq⟩ := mkCoverConstrs_mem g.edges c hc'
  rw [hceq]
  simp only [Constr.sat, evalSum, evalLit]
  have := h (u, v) he
  cases hu : f u <;> cases hv : f v <;> simp_all

/-- The OPB value of `f` is the number of selected vertices. -/
theorem vcObjective_opbVal (g : Graph) (f : Valuation) :
    PBCatcher.Reflect.opbVal (vcObjective g) 0 f = (countTrue f g.numVerts : Int) := by
  simp only [PBCatcher.Reflect.opbVal, PBCatcher.Reflect.objVal, vcObjective, evalSum_posLits]
  omega

/-- Bridge: the bounds `k ≤ |C| ≤ k` over the edge constraints give the
vertex cover number `k`. -/
theorem vertexCoverNumber_of_bounds (g : Graph) (k : Nat)
    (_hedges : edgesInRange g = true)
    (h : PBCatcher.Reflect.formulaBounds (encodeVC g) (vcObjective g) 0
      (some (k : Int)) (some (k : Int))) :
    vertexCoverNumber g k := by
  obtain ⟨hlb, hub⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨ρ, hρ, hval⟩ := hub
    have hv : PBCatcher.Reflect.opbVal (vcObjective g) 0 ρ ≤ (k : Int) := hval
    rw [vcObjective_opbVal] at hv
    exact ⟨ρ, encodeVC_sat_cover g ρ hρ, by omega⟩
  · intro f hcover
    have hv := hlb f (cover_sat_encodeVC g f hcover)
    have hv' : (k : Int) ≤ PBCatcher.Reflect.opbVal (vcObjective g) 0 f := hv
    rw [vcObjective_opbVal] at hv'
    omega

-- Elaboration command

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

/-- `vertex_cover_reflect name g k "proof.pbp"`: the vertex cover number `k`
of `g` from one VeriPB optimization proof of `min: +1 x_1 ... +1 x_n` over
the edge constraints (`conclusion BOUNDS k : id k : solution`), by native
evaluation of `checkProofClaimBool`; `edgesInRange g` is checked by `decide`.
This records a per-use axiom `checkProofClaimBool ... = true`
(`_native.vertex_cover_reflect.ax_*`, the same mechanism as `native_decide`;
see `mkFormulaUnsatProof`). -/
elab "vertex_cover_reflect " n:ident ppSpace gExpr:term:max
    ppSpace kTerm:num ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let proofPath := proofFile.getString
  liftTermElabM do
    let gVal ← Lean.Elab.Term.elabTerm gExpr (some (mkConst ``Graph))
    let gVal ← instantiateMVars gVal
    let k := kTerm.getNat
    let kVal := mkRawNatLit k
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath)
    let constrsExpr := mkApp (mkConst ``encodeVC) gVal
    let numVarsExpr := mkApp (mkConst ``Graph.numVerts) gVal
    let objExpr := mkApp (mkConst ``vcObjective) gVal
    let offsetExpr := toExpr (0 : Int)
    let hedgesVal ← whnfD (mkApp (mkConst ``edgesInRange) gVal)
    unless hedgesVal.isConstOf ``Bool.true do
      throwError "vertex_cover_reflect: an edge of the graph leaves the vertex range 0..n-1"
    let hedgesType := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Bool)
      (mkApp (mkConst ``edgesInRange) gVal) (mkConst ``Bool.true)
    let hedgesProof ← mkDecideProof hedgesType
    let claim := PBCatcher.Reflect.Claim.bounds (some (k : Int)) (some (k : Int))
    let boundsProof ← PBCatcher.Reflect.mkClaimProof `vertex_cover_reflect
      constrsExpr numVarsExpr objExpr offsetExpr proofStr claim
      (ref? := some (← getRef))
    let finalProof := mkApp4 (mkConst ``vertexCoverNumber_of_bounds) gVal kVal
      hedgesProof boundsProof
    let finalType := mkApp2 (mkConst ``vertexCoverNumber) gVal kVal
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : vertexCoverNumber G {k} (reflection)"

end VertexCover

-- ============================================================
-- Vertex cover numbers from single optimization proofs
-- (RoundingSat `--opt-mode=linear --lp=0`, elaborated by VeriPB).
-- ============================================================

namespace VertexCoverShowcase

section VertexCoverOptions
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open IndependentSet VertexCover

vertex_cover_reflect petersen_tau petersen 6
  "applications/vcover/petersen_vc_kernel.pbp"
vertex_cover_reflect paley13_tau (paley 13) 10
  "applications/vcover/Paley_13_vc_kernel.pbp"
vertex_cover_reflect paley17_tau (paley 17) 14
  "applications/vcover/Paley_17_vc_kernel.pbp"
vertex_cover_reflect paley29_tau (paley 29) 25
  "applications/vcover/Paley_29_vc_kernel.pbp"

end VertexCoverOptions

end VertexCoverShowcase
