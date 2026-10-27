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
import PBCatcher.VertexCover

/-!
# Trusted Chromatic Number Encoding (optimization form)

The chromatic number from one VeriPB optimization proof. With `n` vertices
and `k` colours available, variable `x_{v,c}` (index `v*k + c`) says that
vertex `v` has colour `c`, and `y_c` (index `n*k + c`) that colour `c` is
used. The constraints, in this order, are

* per vertex `v`: `Σ_c x_{v,c} ≥ 1`,
* per edge `(u,v)` and colour `c`: `¬x_{u,c} + ¬x_{v,c} ≥ 1`,
* per vertex `v` and colour `c`: `¬x_{v,c} + y_c ≥ 1`,

and the objective is `min: Σ_c y_c`. A `conclusion BOUNDS χ : id χ :
solution` speaks only about colourings with at most `k` colours, but the
bound itself gives `χ ≤ k`, so the bridge theorem concludes that `χ` is the
chromatic number without a side condition on `k`.

## Main definitions

* `Chromatic.encodeChrom` — the constraints above
* `Chromatic.chromObjective` — the objective `Σ_c y_c` (offset 0)
* `Chromatic.chromaticNumber` — mathematical predicate
* `Chromatic.chromaticNumber_of_bounds` — bridge theorem
* `chromatic_reflect` — elaboration command
-/

namespace Chromatic

open OptCount (edgesInRange edgesInRange_spec)

open Sat.PB IndependentSet OptCount

-- Graphs

/-- The Grötzsch graph, Mycielski(C5): cycle `0..4`, copies `5..9` (copy
`5+v` is adjacent to the cycle neighbours of `v`), apex `10` adjacent to all
copies. The edges are sorted pairs in lexicographic order, as in
`applications/gen_opt_instances.py`. -/
def groetzsch : Graph :=
  ⟨11, [(0, 1), (0, 4), (0, 6), (0, 9), (1, 2), (1, 5), (1, 7), (2, 3), (2, 6),
        (2, 8), (3, 4), (3, 7), (3, 9), (4, 5), (4, 8), (5, 10), (6, 10), (7, 10),
        (8, 10), (9, 10)]⟩

-- Mathematical predicates

/-- `col` is a proper colouring of `g` with colours `0..c-1`. -/
def isProperColoring (g : Graph) (c : Nat) (col : Nat → Nat) : Prop :=
  (∀ v, v < g.numVerts → col v < c) ∧ ∀ e ∈ g.edges, col e.1 ≠ col e.2

/-- `g` has a proper colouring with at most `c` colours. -/
def hasColoring (g : Graph) (c : Nat) : Prop :=
  ∃ col : Nat → Nat, isProperColoring g c col

/-- `c` is the chromatic number of `g`: `g` is `c`-colourable, and every
proper colouring of `g` with colours `0..c'-1` has `c ≤ c'`. -/
def chromaticNumber (g : Graph) (c : Nat) : Prop :=
  hasColoring g c ∧ ∀ c', hasColoring g c' → c ≤ c'

-- Encoding

/-- `Σ_c x_{v,c} ≥ 1`. -/
def vertexConstr (k v : Nat) : Constr :=
  ⟨(List.range k).map fun c => (1, Literal.pos (v * k + c)), 1⟩

/-- `¬x_{u,c} + ¬x_{v,c} ≥ 1` per edge and colour, edge-major. -/
def edgeConstrs (k : Nat) (es : List (Nat × Nat)) : List Constr :=
  es.flatMap fun e => (List.range k).map fun c =>
    ⟨[(1, Literal.neg (e.1 * k + c)), (1, Literal.neg (e.2 * k + c))], 1⟩

/-- `¬x_{v,c} + y_c ≥ 1` per vertex and colour, vertex-major. -/
def linkConstrs (n k : Nat) : List Constr :=
  (List.range n).flatMap fun v => (List.range k).map fun c =>
    ⟨[(1, Literal.neg (v * k + c)), (1, Literal.pos (n * k + c))], 1⟩

/-- The constraints of the `k`-colour encoding, in OPB file order. -/
def encodeChrom (g : Graph) (k : Nat) : Array Constr :=
  ((List.range g.numVerts).map (vertexConstr k) ++ edgeConstrs k g.edges ++
    linkConstrs g.numVerts k).toArray

/-- The objective `Σ_c y_c` (offset 0). -/
def chromObjective (g : Graph) (k : Nat) : PBCatcher.Reflect.Objective :=
  (List.range k).map fun c => (1, Literal.pos (g.numVerts * k + c))

/-- Number of variables: `n*k` colour variables and `k` usage variables. -/
def chromNumVars (g : Graph) (k : Nat) : Nat := g.numVerts * k + k

-- Index arithmetic

theorem idx_div {k v a : Nat} (ha : a < k) : (v * k + a) / k = v := by
  rw [show v * k + a = a + v * k by omega, Nat.add_mul_div_right _ _ (by omega),
    Nat.div_eq_of_lt ha, Nat.zero_add]

theorem idx_mod {k v a : Nat} (ha : a < k) : (v * k + a) % k = a := by
  rw [show v * k + a = a + v * k by omega, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt ha]

theorem idx_lt {n k v a : Nat} (hv : v < n) (ha : a < k) : v * k + a < n * k := by
  have h := Nat.mul_le_mul_right k (show v + 1 ≤ n by omega)
  rw [Nat.succ_mul] at h
  omega

-- Membership in the encoding

theorem mem_encodeChrom (g : Graph) (k : Nat) (c : Constr) :
    c ∈ (encodeChrom g k).toList ↔
      c ∈ (List.range g.numVerts).map (vertexConstr k) ∨ c ∈ edgeConstrs k g.edges ∨
        c ∈ linkConstrs g.numVerts k := by
  simp [encodeChrom]

theorem vertexConstr_mem (g : Graph) (k v : Nat) (hv : v < g.numVerts) :
    vertexConstr k v ∈ (encodeChrom g k).toList :=
  (mem_encodeChrom g k _).2 (Or.inl (List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩))

theorem edgeConstr_mem (g : Graph) (k u v a : Nat) (he : (u, v) ∈ g.edges)
    (ha : a < k) :
    (⟨[(1, Literal.neg (u * k + a)), (1, Literal.neg (v * k + a))], 1⟩ : Constr) ∈
      (encodeChrom g k).toList :=
  (mem_encodeChrom g k _).2 (Or.inr (Or.inl (List.mem_flatMap.2
    ⟨(u, v), he, List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩⟩)))

theorem linkConstr_mem (g : Graph) (k v a : Nat) (hv : v < g.numVerts) (ha : a < k) :
    (⟨[(1, Literal.neg (v * k + a)), (1, Literal.pos (g.numVerts * k + a))], 1⟩ :
      Constr) ∈ (encodeChrom g k).toList :=
  (mem_encodeChrom g k _).2 (Or.inr (Or.inr (List.mem_flatMap.2
    ⟨v, List.mem_range.2 hv, List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩⟩)))

-- Objective value

/-- The OPB value is the number of used colours. -/
theorem chromObjective_opbVal (g : Graph) (k : Nat) (f : Valuation) :
    PBCatcher.Reflect.opbVal (chromObjective g k) 0 f =
      (countTrue (fun c => f (g.numVerts * k + c)) k : Int) := by
  simp only [PBCatcher.Reflect.opbVal, PBCatcher.Reflect.objVal, chromObjective,
    evalSum_posLits_shift]
  omega

-- From a solution to a colouring

theorem vertexConstr_sat_exists (k v : Nat) (f : Valuation)
    (h : (vertexConstr k v).sat f) : ∃ a, a < k ∧ f (v * k + a) = true := by
  simp only [vertexConstr, Constr.sat, evalSum_posLits_shift] at h
  exact countTrue_pos_exists _ k (by omega)

/-- A solution with `u` used colours yields a proper colouring with
colours `0..u-1` (each used colour is renamed to its rank). -/
theorem coloring_of_sat (g : Graph) (k : Nat)
    (hedges : ∀ e ∈ g.edges, e.1 < g.numVerts ∧ e.2 < g.numVerts)
    (ρ : Valuation) (hρ : PBCatcher.Reflect.FormulaSat (encodeChrom g k) ρ) :
    hasColoring g (countTrue (fun c => ρ (g.numVerts * k + c)) k) := by
  let y : Nat → Bool := fun c => ρ (g.numVerts * k + c)
  have hpick : ∀ v, ∃ a, v < g.numVerts → a < k ∧ ρ (v * k + a) = true := by
    intro v
    by_cases hv : v < g.numVerts
    · obtain ⟨a, ha, hx⟩ := vertexConstr_sat_exists k v ρ (hρ _ (vertexConstr_mem g k v hv))
      exact ⟨a, fun _ => ⟨ha, hx⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  let pick : Nat → Nat := fun v => Classical.choose (hpick v)
  have hpick_spec : ∀ v, v < g.numVerts → pick v < k ∧ ρ (v * k + pick v) = true :=
    fun v => Classical.choose_spec (hpick v)
  -- the chosen colour of an in-range vertex is used
  have hused : ∀ v, v < g.numVerts → y (pick v) = true := by
    intro v hv
    obtain ⟨ha, hx⟩ := hpick_spec v hv
    have hl := hρ _ (linkConstr_mem g k v (pick v) hv ha)
    simp only [Constr.sat, evalSum, evalLit, hx] at hl
    show ρ (g.numVerts * k + pick v) = true
    cases hy : ρ (g.numVerts * k + pick v) <;> simp_all
  refine ⟨fun v => countTrue y (pick v), ?_, ?_⟩
  · intro v hv
    exact countTrue_lt_of_true y (hused v hv) (hpick_spec v hv).1
  · intro e he heq
    obtain ⟨hu, hv⟩ := hedges e he
    have hsame : pick e.1 = pick e.2 :=
      countTrue_inj y (hused e.1 hu) (hused e.2 hv) heq
    obtain ⟨ha, hxu⟩ := hpick_spec e.1 hu
    obtain ⟨_, hxv⟩ := hpick_spec e.2 hv
    have hc := hρ _ (edgeConstr_mem g k e.1 e.2 (pick e.1) he ha)
    rw [← hsame] at hxv
    simp only [Constr.sat, evalSum, evalLit, hxu, hxv] at hc
    simp at hc

-- From a colouring to a solution

/-- The valuation of a colouring `col` with colours `0..c'-1`: `x_{v,a}`
iff `col v = a`, and `y_a` iff `a < c'`. -/
def colorVal (n k c' : Nat) (col : Nat → Nat) : Valuation := fun i =>
  if i < n * k then decide (col (i / k) = i % k) else decide (i - n * k < c')

theorem colorVal_x {n k c' v a : Nat} (col : Nat → Nat) (hv : v < n) (ha : a < k) :
    colorVal n k c' col (v * k + a) = decide (col v = a) := by
  simp only [colorVal, if_pos (idx_lt hv ha), idx_div ha, idx_mod ha]

theorem colorVal_y {n k c' : Nat} (col : Nat → Nat) (a : Nat) :
    colorVal n k c' col (n * k + a) = decide (a < c') := by
  simp only [colorVal, show ¬ n * k + a < n * k by omega, ↓reduceIte,
    show n * k + a - n * k = a by omega]

theorem colorVal_sat (g : Graph) (k c' : Nat) (col : Nat → Nat)
    (hedges : ∀ e ∈ g.edges, e.1 < g.numVerts ∧ e.2 < g.numVerts)
    (hcol : isProperColoring g c' col) (hck : c' ≤ k) :
    PBCatcher.Reflect.FormulaSat (encodeChrom g k) (colorVal g.numVerts k c' col) := by
  obtain ⟨hrange, hproper⟩ := hcol
  intro c hc
  rcases (mem_encodeChrom g k c).1 hc with hc | hc | hc
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hc
    have hv := List.mem_range.1 hv
    have hcv := hrange v hv
    simp only [vertexConstr, Constr.sat, evalSum_posLits_shift]
    have hp : colorVal g.numVerts k c' col (v * k + col v) = true := by
      rw [colorVal_x col hv (by omega)]; simp
    have := countTrue_lt_of_true (fun a => colorVal g.numVerts k c' col (v * k + a))
      hp (show col v < k by omega)
    omega
  · obtain ⟨e, he, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
    have ha := List.mem_range.1 ha
    obtain ⟨hu, hv⟩ := hedges e he
    have hne := hproper e he
    simp only [Constr.sat, evalSum, evalLit, colorVal_x col hu ha, colorVal_x col hv ha]
    by_cases h1 : col e.1 = a <;> by_cases h2 : col e.2 = a <;> simp_all
  · obtain ⟨v, hv, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
    have hv := List.mem_range.1 hv
    have ha := List.mem_range.1 ha
    have hcv := hrange v hv
    simp only [Constr.sat, evalSum, evalLit, colorVal_x col hv ha, colorVal_y col a]
    by_cases h1 : col v = a
    · subst h1; simp [hcv]
    · simp [h1]

/-- Bridge: the bounds `χ ≤ Σ_c y_c ≤ χ` of the `k`-colour encoding give the
chromatic number `χ`. The lower bound covers only colourings with at most `k`
colours; the solution of the upper bound shows `χ ≤ k`, which covers the
rest. -/
theorem chromaticNumber_of_bounds (g : Graph) (k c : Nat)
    (hedges : edgesInRange g = true)
    (h : PBCatcher.Reflect.formulaBounds (encodeChrom g k) (chromObjective g k) 0
      (some (c : Int)) (some (c : Int))) :
    chromaticNumber g c := by
  have hedges := edgesInRange_spec g hedges
  obtain ⟨hlb, hub⟩ := h
  obtain ⟨ρ, hρ, hval⟩ := hub
  have hv : PBCatcher.Reflect.opbVal (chromObjective g k) 0 ρ ≤ (c : Int) := hval
  rw [chromObjective_opbVal] at hv
  have hv2 : (c : Int) ≤ PBCatcher.Reflect.opbVal (chromObjective g k) 0 ρ := hlb ρ hρ
  rw [chromObjective_opbVal] at hv2
  have hle := countTrue_le (fun a => ρ (g.numVerts * k + a)) k
  refine ⟨?_, ?_⟩
  · obtain ⟨col, hrange, hproper⟩ := coloring_of_sat g k hedges ρ hρ
    exact ⟨col, fun v hv' => by have := hrange v hv'; omega, hproper⟩
  · intro c' ⟨col, hcol⟩
    rcases Nat.lt_or_ge c' k with hck | hck
    · have hs := colorVal_sat g k c' col hedges hcol (by omega)
      have hl : (c : Int) ≤ PBCatcher.Reflect.opbVal (chromObjective g k) 0
          (colorVal g.numVerts k c' col) := hlb _ hs
      rw [chromObjective_opbVal] at hl
      have hcount : countTrue (fun a => colorVal g.numVerts k c' col (g.numVerts * k + a)) k
          = countTrue (fun a => decide (a < c')) k := by
        simp only [colorVal_y]
      rw [hcount, countTrue_lt_const] at hl
      omega
    · omega

-- Elaboration command

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

/-- `chromatic_reflect name g k χ "proof.pbp"`: the chromatic number `χ` of
`g` from one VeriPB optimization proof of the `k`-colour encoding
(`conclusion BOUNDS χ : id χ : solution`), by native evaluation of
`checkProofClaimBool`; `edgesInRange g` is checked by `decide`. This records
a per-use axiom `checkProofClaimBool ... = true`
(`_native.chromatic_reflect.ax_*`, the same mechanism as `native_decide`; see
`mkFormulaUnsatProof`). -/
elab "chromatic_reflect " n:ident ppSpace gExpr:term:max
    ppSpace kTerm:num ppSpace cTerm:num ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let proofPath := proofFile.getString
  liftTermElabM do
    let gVal ← Lean.Elab.Term.elabTerm gExpr (some (mkConst ``Graph))
    let gVal ← instantiateMVars gVal
    let k := kTerm.getNat
    let kVal := mkRawNatLit k
    let c := cTerm.getNat
    let cVal := mkRawNatLit c
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath)
    let constrsExpr := mkApp2 (mkConst ``encodeChrom) gVal kVal
    let numVarsExpr := mkApp2 (mkConst ``chromNumVars) gVal kVal
    let objExpr := mkApp2 (mkConst ``chromObjective) gVal kVal
    let offsetExpr := toExpr (0 : Int)
    let hedgesVal ← whnfD (mkApp (mkConst ``edgesInRange) gVal)
    unless hedgesVal.isConstOf ``Bool.true do
      throwError "chromatic_reflect: an edge of the graph leaves the vertex range 0..n-1"
    let claim := PBCatcher.Reflect.Claim.bounds (some (c : Int)) (some (c : Int))
    let boundsProof ← PBCatcher.Reflect.mkClaimProof `chromatic_reflect
      constrsExpr numVarsExpr objExpr offsetExpr proofStr claim
      (ref? := some (← getRef))
    let hedgesType := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Bool)
      (mkApp (mkConst ``edgesInRange) gVal) (mkConst ``Bool.true)
    let hedgesProof ← mkDecideProof hedgesType
    let finalProof := mkApp5 (mkConst ``chromaticNumber_of_bounds) gVal kVal cVal
      hedgesProof boundsProof
    let finalType := mkApp2 (mkConst ``chromaticNumber) gVal cVal
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : chromaticNumber G {c} (reflection)"

end Chromatic

-- ============================================================
-- Chromatic numbers from single optimization proofs
-- (RoundingSat `--opt-mode=linear --lp=0`, elaborated by VeriPB).
-- ============================================================

namespace ChromaticShowcase

section ChromaticOptions
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open IndependentSet VertexCover Chromatic

-- Petersen graph, 4 colours available: χ = 3
chromatic_reflect petersen_chi petersen 4 3
  "applications/chromatic/petersen_k4_kernel.pbp"
-- Grötzsch graph (Mycielski(C5)), 5 colours available: χ = 4
chromatic_reflect groetzsch_chi groetzsch 5 4
  "applications/chromatic/groetzsch_k5_kernel.pbp"

end ChromaticOptions

end ChromaticShowcase
