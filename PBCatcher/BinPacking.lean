/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import Lean
import Std
import PBCatcher.PseudoBoolean
import PBCatcher.FromVeriPB
import PBCatcher.Reflect
import PBCatcher.IndependentSet

/-!
# Trusted Bin Packing Encoding

End-to-end verified bin packing impossibility: Lean encodes the bin
packing decision problem as PB constraints, verifies a VeriPB kernel
proof, and produces a mathematical theorem that a set of items cannot
fit into the given number of bins with the given capacity.

Given items with sizes s_0, ..., s_{n-1}, m bins each of capacity C,
the question is whether there exists an assignment of items to bins
such that the total size in each bin is at most C.

## Main results

* `BinPacking.bp12_5_impossible` -- 12 items of sizes [10,9,8,8,6,5,4,4,4,4,4,4]
  do not fit into 5 bins of capacity 14
* `BinPacking.bp12_m6_minBins`, `bp12_m7_minBins` -- 6 bins are the minimum
  (one optimization proof each, with 6 or 7 bins available)

## Infrastructure

* `BinPacking.encode` -- PB constraint encoding
* `BinPacking.no_packing_of_unsat` -- encoding soundness
* `binpack_reflect` -- elaboration command
* `BinPacking.encodeOpt`, `minBins`, `minBins_of_bounds`, `binpack_opt_reflect`
  -- optimization form (minimum number of bins)
-/

namespace BinPacking

open Sat.PB

-- Instance

/-- A bin packing instance: item sizes, number of bins, bin capacity. -/
structure Instance where
  sizes : List Nat
  numBins : Nat
  capacity : Nat
  deriving Repr

/-- Number of items. -/
def Instance.numItems (inst : Instance) : Nat := inst.sizes.length

/-- Total size of all items. -/
def Instance.totalSize (inst : Instance) : Nat := inst.sizes.foldl (· + ·) 0

-- Variable indexing

/-- Variable index for "item i is in bin j" with m bins. -/
def varIdx (m : Nat) (i j : Nat) : Nat := i * m + j

theorem varIdx_div {m i j : Nat} (hm : 0 < m) (hj : j < m) :
    varIdx m i j / m = i := by
  simp only [varIdx]
  rw [show i * m + j = j + i * m by omega]
  rw [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hj, Nat.zero_add]

theorem varIdx_mod {m i j : Nat} (_hm : 0 < m) (hj : j < m) :
    varIdx m i j % m = j := by
  simp only [varIdx]
  rw [show i * m + j = j + i * m by omega]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

-- Mathematical predicate

/-- Load of bin j under assignment assign: sum of sizes[k] for k < bound with assign k = j. -/
def binLoad (sizes : List Nat) (assign : Nat → Nat) (j : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (if assign k = j then sizes[k]! else 0) + binLoad sizes assign j k

/-- A valid packing: each item goes to a valid bin, each bin within capacity. -/
def isValidPacking (inst : Instance) (assign : Nat → Nat) : Prop :=
  (∀ i, i < inst.numItems → assign i < inst.numBins) ∧
  (∀ j, j < inst.numBins → binLoad inst.sizes assign j inst.numItems ≤ inst.capacity)

/-- The instance has a valid packing. -/
def hasPacking (inst : Instance) : Prop :=
  ∃ assign : Nat → Nat, isValidPacking inst assign

-- Encoding

/-- Assignment constraint for item i: item must go in at least one bin. -/
def mkAssignConstr (m : Nat) (i : Nat) : Constr :=
  ⟨(List.range m).map fun j => (1, Literal.pos (varIdx m i j)), 1⟩

/-- Capacity constraint for bin j (negated form):
    sum_i sizes[i] * neg(x_{i,j}) >= totalSize - capacity. -/
def mkCapConstr (inst : Instance) (j : Nat) : Constr :=
  ⟨(List.range inst.numItems).map fun i =>
    (inst.sizes[i]!, Literal.neg (varIdx inst.numBins i j)),
   inst.totalSize - inst.capacity⟩

/-- Full encoding: n assignment constraints + m capacity constraints. -/
def encode (inst : Instance) : Array Constr :=
  let assignConstrs := (List.range inst.numItems).map (mkAssignConstr inst.numBins)
  let capConstrs := (List.range inst.numBins).map (mkCapConstr inst)
  (assignConstrs ++ capConstrs).toArray

-- Valuation from packing

/-- Valuation encoding an assignment: variable v encodes "item v/m is in bin v%m". -/
def packingVal (m : Nat) (assign : Nat → Nat) (v : Nat) : Bool :=
  if m == 0 then false else assign (v / m) == (v % m)

-- Helper lemmas

private theorem beq_nat_false_of_pos {m : Nat} (hm : 0 < m) : (m == 0) = false := by
  simp [Nat.ne_of_gt hm]

theorem evalLit_pos_packingVal (m : Nat) (assign : Nat → Nat) (i j : Nat)
    (hm : 0 < m) (hj : j < m) :
    evalLit (packingVal m assign) (Literal.pos (varIdx m i j)) =
      if assign i = j then 1 else 0 := by
  simp only [evalLit, packingVal, varIdx_div hm hj, varIdx_mod hm hj,
    beq_nat_false_of_pos hm, Bool.false_eq_true, ↓reduceIte]
  cases h : (assign i == j)
  · simp only [beq_eq_false_iff_ne] at h; simp [h]
  · simp only [beq_iff_eq] at h; simp [h]

theorem evalLit_neg_packingVal (m : Nat) (assign : Nat → Nat) (i j : Nat)
    (hm : 0 < m) (hj : j < m) :
    evalLit (packingVal m assign) (Literal.neg (varIdx m i j)) =
      if assign i = j then 0 else 1 := by
  simp only [evalLit, packingVal, varIdx_div hm hj, varIdx_mod hm hj,
    beq_nat_false_of_pos hm, Bool.false_eq_true, ↓reduceIte]
  cases h : (assign i == j)
  · simp only [beq_eq_false_iff_ne] at h; simp [h]
  · simp only [beq_iff_eq] at h; simp [h]

theorem evalSum_ge_mem (f : Valuation) :
    ∀ (ts : List Term) (t : Term), t ∈ ts →
    t.1 * evalLit f t.2 ≤ evalSum f ts := by
  intro ts t hmem; induction ts with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons hd tl ih =>
    simp only [evalSum]
    rcases List.mem_cons.mp hmem with rfl | htl
    · omega
    · have := ih htl; omega

-- Soundness: assignment constraints

theorem assignConstr_sat (m : Nat) (assign : Nat → Nat) (i : Nat)
    (hm : 0 < m) (hbin : assign i < m) :
    (mkAssignConstr m i).sat (packingVal m assign) := by
  simp only [Constr.sat, mkAssignConstr]
  have hmem : (1, Literal.pos (varIdx m i (assign i))) ∈
      (List.range m).map fun j => (1, Literal.pos (varIdx m i j)) :=
    List.mem_map.mpr ⟨assign i, List.mem_range.mpr hbin, rfl⟩
  have hge := evalSum_ge_mem (packingVal m assign) _ _ hmem
  rw [evalLit_pos_packingVal m assign i (assign i) hm hbin] at hge
  simp at hge; omega

-- Soundness: capacity constraints
-- Strategy: connect evalSum of negated literals to sumIf, use complement identity

/-- Sum of sizes[k] for k < bound where p k is true. -/
def sumIf (sizes : List Nat) (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => (if p k then sizes[k]! else 0) + sumIf sizes p k

/-- Sum of all sizes[k] for k < bound. -/
def sumAll (sizes : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sizes[k]! + sumAll sizes k

theorem sumIf_complement (sizes : List Nat) (p : Nat → Bool) :
    ∀ k, sumIf sizes p k + sumIf sizes (fun i => !p i) k = sumAll sizes k := by
  intro k; induction k with
  | zero => simp [sumIf, sumAll]
  | succ n ih =>
    show (if p n = true then sizes[n]! else 0) + sumIf sizes p n +
        ((if (!p n) = true then sizes[n]! else 0) + sumIf sizes (fun i => !p i) n) =
        sizes[n]! + sumAll sizes n
    have hrearr : (if p n = true then sizes[n]! else 0) + sumIf sizes p n +
        ((if (!p n) = true then sizes[n]! else 0) + sumIf sizes (fun i => !p i) n) =
        ((if p n = true then sizes[n]! else 0) + (if (!p n) = true then sizes[n]! else 0)) +
        (sumIf sizes p n + sumIf sizes (fun i => !p i) n) := by omega
    rw [hrearr, ih]
    cases p n <;> simp

/-- binLoad equals sumIf with the predicate "assign k = j". -/
theorem binLoad_eq_sumIf (sizes : List Nat) (assign : Nat → Nat) (j : Nat) :
    ∀ k, binLoad sizes assign j k = sumIf sizes (fun i => decide (assign i = j)) k := by
  intro k; induction k with
  | zero => simp [binLoad, sumIf]
  | succ n ih =>
    simp only [binLoad, sumIf, ih]
    congr 1
    split
    · next h => simp [h]
    · next h => simp [h]

/-- evalSum of negated literal terms equals sumIf of negated predicate. -/
theorem evalSum_neg_eq_sumIf (sizes : List Nat) (m : Nat) (assign : Nat → Nat) (j : Nat)
    (hm : 0 < m) (hj : j < m) :
    ∀ k, evalSum (packingVal m assign)
      ((List.range k).map fun i => (sizes[i]!, Literal.neg (varIdx m i j))) =
    sumIf sizes (fun i => !(decide (assign i = j))) k := by
  intro k; induction k with
  | zero => simp [evalSum, sumIf]
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      evalSum_append]
    rw [ih]
    simp only [evalSum, Nat.add_zero]
    rw [Nat.add_comm]
    congr 1
    rw [evalLit_neg_packingVal m assign n j hm hj]
    split
    · next h => simp [h]
    · next h => simp [h]

/-- Helper: foldl (· + ·) acc l = acc + foldl (· + ·) 0 l -/
theorem foldl_add_acc : ∀ (l : List Nat) (acc : Nat),
    l.foldl (· + ·) acc = acc + l.foldl (· + ·) 0 := by
  intro l; induction l with
  | nil => simp [List.foldl]
  | cons h t ih =>
    intro acc
    show List.foldl (· + ·) (acc + h) t = acc + List.foldl (· + ·) (0 + h) t
    rw [ih (acc + h), ih (0 + h)]
    omega

/-- sumAll over the full list equals foldl sum. -/
theorem sumAll_eq_foldl (sizes : List Nat) :
    ∀ k, k ≤ sizes.length →
    sumAll sizes k + (sizes.drop k).foldl (· + ·) 0 = sizes.foldl (· + ·) 0 := by
  intro k hk; induction k with
  | zero => simp [sumAll, List.drop]
  | succ n ih =>
    have hn : n < sizes.length := by omega
    simp only [sumAll]
    have hdrop : sizes.drop n = sizes[n] :: sizes.drop (n + 1) :=
      List.drop_eq_getElem_cons hn
    have h_prev := ih (by omega)
    rw [hdrop] at h_prev
    -- h_prev now has foldl (· + ·) (0 + sizes[n]) ...
    -- goal needs foldl (· + ·) 0 (drop (n+1))
    rw [show sizes[n]! = sizes[n] from by simp [getElem!_def, List.getElem?_eq_getElem hn]]
    -- Use foldl_add_acc to rewrite h_prev
    show sizes[n] + sumAll sizes n + List.foldl (· + ·) 0 (sizes.drop (n + 1)) =
        List.foldl (· + ·) 0 sizes
    have hfoldl : List.foldl (· + ·) (0 + sizes[n]) (sizes.drop (n + 1)) =
        sizes[n] + List.foldl (· + ·) 0 (sizes.drop (n + 1)) := by
      rw [foldl_add_acc]; omega
    simp only [List.foldl] at h_prev
    rw [hfoldl] at h_prev
    omega

theorem totalSize_eq_sumAll_full (inst : Instance) :
    inst.totalSize = sumAll inst.sizes inst.numItems := by
  simp only [Instance.totalSize, Instance.numItems]
  have h := sumAll_eq_foldl inst.sizes inst.sizes.length (Nat.le_refl _)
  simp [List.drop_length] at h
  omega

theorem capConstr_sat (inst : Instance) (assign : Nat → Nat) (j : Nat)
    (hm : 0 < inst.numBins) (hj : j < inst.numBins)
    (hcap : binLoad inst.sizes assign j inst.numItems ≤ inst.capacity)
    (hle : inst.capacity ≤ inst.totalSize) :
    (mkCapConstr inst j).sat (packingVal inst.numBins assign) := by
  simp only [Constr.sat, mkCapConstr]
  rw [evalSum_neg_eq_sumIf inst.sizes inst.numBins assign j hm hj inst.numItems]
  -- Need: inst.totalSize - inst.capacity ≤ sumIf(¬inBin, n)
  -- From complement: sumIf(inBin) + sumIf(¬inBin) = sumAll = totalSize
  -- From hcap: sumIf(inBin) ≤ capacity (after rewriting binLoad)
  -- So: sumIf(¬inBin) = totalSize - sumIf(inBin) ≥ totalSize - capacity
  rw [binLoad_eq_sumIf] at hcap
  have hcomp := sumIf_complement inst.sizes (fun i => decide (assign i = j)) inst.numItems
  rw [totalSize_eq_sumAll_full] at hle
  -- hle : inst.capacity ≤ sumAll inst.sizes inst.numItems
  -- hcomp : sumIf(inBin) + sumIf(¬inBin) = sumAll
  -- hcap : sumIf(inBin) ≤ inst.capacity
  -- goal : inst.totalSize - inst.capacity ≤ sumIf(¬inBin)
  -- Since totalSize = sumAll (from hle direction), and totalSize - cap is Nat sub
  show inst.totalSize - inst.capacity ≤
    sumIf inst.sizes (fun i => !decide (assign i = j)) inst.numItems
  rw [totalSize_eq_sumAll_full]
  omega

-- Main soundness theorem

theorem encode_mem_sat (inst : Instance) (assign : Nat → Nat)
    (hm : 0 < inst.numBins)
    (hle : inst.capacity ≤ inst.totalSize)
    (hpacking : isValidPacking inst assign) :
    ∀ c ∈ (encode inst).toList, c.sat (packingVal inst.numBins assign) := by
  intro c hc
  have henc : (encode inst).toList =
      (List.range inst.numItems).map (mkAssignConstr inst.numBins) ++
      (List.range inst.numBins).map (mkCapConstr inst) := by
    simp [encode]
  rw [henc] at hc
  simp only [List.mem_append] at hc
  obtain ⟨hbin, hcapacity⟩ := hpacking
  rcases hc with hc | hc
  · simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    exact assignConstr_sat inst.numBins assign i hm (hbin i hi)
  · simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    exact capConstr_sat inst assign j hm hj (hcapacity j hj) hle

/-- If the encoding is UNSAT, no valid packing exists (assuming capacity <= totalSize). -/
theorem no_packing_of_unsat (inst : Instance)
    (hm : 0 < inst.numBins)
    (hle : inst.capacity ≤ inst.totalSize)
    (hunsat : ∀ v : Valuation, ∃ c ∈ (encode inst).toList, ¬c.sat v) :
    ¬hasPacking inst := by
  intro ⟨assign, hpacking⟩
  obtain ⟨c, hc, hnsat⟩ := hunsat (packingVal inst.numBins assign)
  exact hnsat (encode_mem_sat inst assign hm hle hpacking c hc)

-- OPB generation

/-- Generate OPB format string for the bin packing encoding. -/
def toOPB (inst : Instance) : String := Id.run do
  let n := inst.numItems
  let m := inst.numBins
  let totalVars := n * m
  let numConstrs := n + m
  let mut s := s!"* #variable= {totalVars} #constraint= {numConstrs} #equal= 0 intsize= 6\n"
  for i in List.range n do
    for j in List.range m do
      s := s ++ s!"+1 x{varIdx m i j + 1} "
    s := s ++ ">= 1 ;\n"
  let ts := inst.totalSize
  for j in List.range m do
    for i in List.range n do
      s := s ++ s!"+{inst.sizes[i]!} ~x{varIdx m i j + 1} "
    s := s ++ s!">= {ts - inst.capacity} ;\n"
  return s

-- Elaboration commands

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

-- Reflection-based verification
elab "binpack_reflect " nm:ident ppSpace instTerm:term:max ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let proofPath := proofFile.getString
  liftTermElabM do
    let instExpr ← Lean.Elab.Term.elabTerm instTerm (some (mkConst ``Instance))
    let instExpr ← instantiateMVars instExpr
    -- Reduce to get concrete values for numItems, numBins
    let instVal ← withTransparency .all <| reduce instExpr
    -- Extract fields: Instance.mk sizes numBins capacity (3 explicit args)
    let some (sizesExpr, numBinsExpr, _capExpr) := instVal.app3? ``Instance.mk
      | throwError "could not reduce Instance to Instance.mk"
    let numItemsExpr := mkApp2 (mkConst ``List.length [.zero]) (mkConst ``Nat) sizesExpr
    let numItemsVal ← withTransparency .all <| reduce numItemsExpr
    let some numItems := numItemsVal.rawNatLit?
      | throwError "could not reduce numItems to a literal"
    let numBinsVal ← withTransparency .all <| reduce numBinsExpr
    let some numBins := numBinsVal.rawNatLit?
      | throwError "could not reduce numBins to a literal"
    let numVars := numItems * numBins
    let numVarsExpr := mkRawNatLit numVars
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath)
    let constrsExpr := mkApp (mkConst ``encode) instExpr
    let proofStrExpr := mkStrLit proofStr
    let checkExpr := mkApp5 (mkConst ``PBCatcher.Reflect.checkProofBool)
      constrsExpr numVarsExpr
      PBCatcher.Reflect.emptyObjectiveExpr PBCatcher.Reflect.emptyNamesExpr
      proofStrExpr
    let hEqTrue ← match ← Lean.Meta.nativeEqTrue `binpack_reflect checkExpr
        (axiomDeclRange? := (← getRef)) with
      | .success prf => pure prf
      | .notTrue => throwError "Reflection checker returned false for {name}"
    let unsatProof := mkApp6
      (mkConst ``PBCatcher.Reflect.checkProof_sound)
      constrsExpr numVarsExpr
      PBCatcher.Reflect.emptyObjectiveExpr PBCatcher.Reflect.emptyNamesExpr
      proofStrExpr hEqTrue
    -- Build side-condition proofs via mkDecideProof
    if numBins == 0 then throwError "numBins must be positive"
    let hmType := mkApp4 (mkConst ``LT.lt [.zero])
      (mkConst ``Nat) (mkConst ``instLTNat) (mkRawNatLit 0)
      (mkApp (mkConst ``Instance.numBins) instExpr)
    let hmProof ← mkDecideProof hmType
    let hleType := mkApp4 (mkConst ``LE.le [.zero])
      (mkConst ``Nat) (mkConst ``instLENat)
      (mkApp (mkConst ``Instance.capacity) instExpr)
      (mkApp (mkConst ``Instance.totalSize) instExpr)
    let hleProof ← mkDecideProof hleType
    let finalProof := mkApp4 (mkConst ``no_packing_of_unsat)
      instExpr hmProof hleProof unsatProof
    let finalType := mkApp (mkConst ``Not)
      (mkApp (mkConst ``hasPacking) instExpr)
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : ¬ hasPacking"

-- Concrete instance

/-- 12 items (sizes [10,9,8,8,6,5,4,4,4,4,4,4]), 5 bins, capacity 14.
    Total size = 70 = 5×14, so not refutable by total weight alone.
    UNSAT via rounding: with m=4, heavy items (≥8) need 2 slots,
    light items (≥4) need 1 slot, each bin has ≤3 slots (14/4=3),
    but total demand is 2×4+8=16 > 15=3×5. Not AMO-reducible:
    pairs like 10+4=14 and triples like 4+4+4=12 fit. -/
def inst12_5 : Instance :=
  { sizes := [10, 9, 8, 8, 6, 5, 4, 4, 4, 4, 4, 4]
    numBins := 5
    capacity := 14 }

-- Impossibility verified via VeriPB reflection checker
binpack_reflect bp12_5_impossible inst12_5
  "applications/binpack/bp12_5_kernel.pbp"

/-! ### Optimization form: the minimum number of bins from one proof

With `m = inst.numBins` bins available, `y_j` (index `n*m + j`) says that bin
`j` is used. The constraints, in OPB file order, are the item constraints
`Σ_j x_{i,j} ≥ 1` and, per bin, `Σ_i s_i ¬x_{i,j} + C y_j ≥ totalSize`
(that is, `Σ_i s_i x_{i,j} ≤ C y_j`); the objective is `min: Σ_j y_j`. A
`conclusion BOUNDS k : id k : solution` speaks only about packings into at
most `m` bins, but the solution gives `k ≤ m`, so the bridge theorem
concludes that `k` bins are the minimum. It assumes positive item sizes
(an item of size 0 could sit in an unused bin). -/

/-- The instance with `k` bins. -/
def Instance.withBins (inst : Instance) (k : Nat) : Instance := { inst with numBins := k }

/-- `k` is the least number of bins of capacity `inst.capacity` that hold
the items (`inst.numBins` is ignored). -/
def minBins (inst : Instance) (k : Nat) : Prop :=
  hasPacking (inst.withBins k) ∧ ∀ k', hasPacking (inst.withBins k') → k ≤ k'

/-- All item sizes are positive. -/
def sizesPositive (inst : Instance) : Bool := inst.sizes.all fun s => decide (0 < s)

theorem sizesPositive_spec (inst : Instance) (h : sizesPositive inst = true) :
    ∀ i, i < inst.numItems → 0 < inst.sizes[i]! := by
  intro i hi
  simp only [sizesPositive, List.all_eq_true, decide_eq_true_eq] at h
  have hi' : i < inst.sizes.length := hi
  rw [show inst.sizes[i]! = inst.sizes[i] from by
    simp [getElem!_def, List.getElem?_eq_getElem hi']]
  exact h _ (List.getElem_mem hi')

/-- Bin `j` holds at most `C`, and nothing unless it is used:
`Σ_i s_i ¬x_{i,j} + C y_j ≥ totalSize`. -/
def mkCapOptConstr (inst : Instance) (j : Nat) : Constr :=
  ⟨(List.range inst.numItems).map (fun i =>
      (inst.sizes[i]!, Literal.neg (varIdx inst.numBins i j))) ++
    [(inst.capacity, Literal.pos (inst.numItems * inst.numBins + j))],
   inst.totalSize⟩

/-- The constraints of the optimization encoding, in OPB file order. -/
def encodeOpt (inst : Instance) : Array Constr :=
  ((List.range inst.numItems).map (mkAssignConstr inst.numBins) ++
    (List.range inst.numBins).map (mkCapOptConstr inst)).toArray

/-- The objective `Σ_j y_j` (offset 0). -/
def binObjective (inst : Instance) : PBCatcher.Reflect.Objective :=
  (List.range inst.numBins).map fun j => (1, Literal.pos (inst.numItems * inst.numBins + j))

/-- Number of variables: `n*m` assignment and `m` usage variables. -/
def Instance.numVarsOpt (inst : Instance) : Nat :=
  inst.numItems * inst.numBins + inst.numBins

-- sumIf lemmas

theorem sumIf_congr (sizes : List Nat) (p q : Nat → Bool) :
    ∀ n, (∀ i, i < n → p i = q i) → sumIf sizes p n = sumIf sizes q n := by
  intro n; induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [sumIf]
    rw [h n (by omega), ih (fun i hi => h i (by omega))]

theorem sumIf_false (sizes : List Nat) : ∀ n, sumIf sizes (fun _ => false) n = 0 := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => simp [sumIf, ih]

theorem sumIf_mono (sizes : List Nat) (p q : Nat → Bool) :
    ∀ n, (∀ i, i < n → p i = true → q i = true) → sumIf sizes p n ≤ sumIf sizes q n := by
  intro n; induction n with
  | zero => intro _; simp [sumIf]
  | succ n ih =>
    intro h
    have := ih (fun i hi => h i (by omega))
    have := h n (by omega)
    simp only [sumIf]
    cases hp : p n <;> cases hq : q n <;> simp_all <;> omega

theorem le_sumIf (sizes : List Nat) (p : Nat → Bool) :
    ∀ n i, i < n → p i = true → sizes[i]! ≤ sumIf sizes p n := by
  intro n; induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi hp
    simp only [sumIf]
    rcases Nat.lt_or_ge i n with hlt | hge
    · have := ih i hlt hp; omega
    · have : i = n := by omega
      subst this; simp [hp]

theorem evalSum_neg_sumIf (f : Valuation) (sizes : List Nat) (m j : Nat) :
    ∀ k, evalSum f ((List.range k).map fun i => (sizes[i]!, Literal.neg (varIdx m i j))) =
      sumIf sizes (fun i => !f (varIdx m i j)) k := by
  intro k; induction k with
  | zero => simp [evalSum, sumIf]
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      evalSum_append]
    rw [ih]
    simp only [evalSum, evalLit, sumIf]
    rcases Bool.eq_false_or_eq_true (f (varIdx m n j)) with h | h <;> simp [h] <;> omega

theorem varIdx_lt {n m i j : Nat} (hi : i < n) (hj : j < m) : varIdx m i j < n * m := by
  have h := Nat.mul_le_mul_right m (show i + 1 ≤ n by omega)
  rw [Nat.succ_mul] at h
  simp only [varIdx]
  omega

-- Membership in the encoding

theorem mem_encodeOpt (inst : Instance) (c : Constr) :
    c ∈ (encodeOpt inst).toList ↔
      c ∈ (List.range inst.numItems).map (mkAssignConstr inst.numBins) ∨
        c ∈ (List.range inst.numBins).map (mkCapOptConstr inst) := by
  simp [encodeOpt]

/-- The load of bin `j` under any solution is at most `C y_j`. -/
theorem capOptConstr_load (inst : Instance) (f : Valuation) (j : Nat)
    (h : (mkCapOptConstr inst j).sat f) :
    sumIf inst.sizes (fun i => f (varIdx inst.numBins i j)) inst.numItems ≤
      inst.capacity * evalLit f (Literal.pos (inst.numItems * inst.numBins + j)) := by
  simp only [mkCapOptConstr, Constr.sat, evalSum_append, evalSum_neg_sumIf] at h
  have hcomp : sumIf inst.sizes (fun i => f (varIdx inst.numBins i j)) inst.numItems +
      sumIf inst.sizes (fun i => !f (varIdx inst.numBins i j)) inst.numItems =
      sumAll inst.sizes inst.numItems :=
    sumIf_complement inst.sizes (fun i => f (varIdx inst.numBins i j)) inst.numItems
  rw [← totalSize_eq_sumAll_full] at hcomp
  simp only [evalSum] at h
  omega

-- Objective value

/-- The OPB value is the number of used bins. -/
theorem binObjective_opbVal (inst : Instance) (f : Valuation) :
    PBCatcher.Reflect.opbVal (binObjective inst) 0 f =
      (IndependentSet.countTrue (fun j => f (inst.numItems * inst.numBins + j))
        inst.numBins : Int) := by
  simp only [PBCatcher.Reflect.opbVal, PBCatcher.Reflect.objVal, binObjective,
    OptCount.evalSum_posLits_shift]
  omega

-- From a solution to a packing

/-- A solution with `u` used bins yields a packing into `u` bins (each used
bin is renamed to its rank). -/
theorem packing_of_sat (inst : Instance) (hpos : ∀ i, i < inst.numItems → 0 < inst.sizes[i]!)
    (ρ : Valuation) (hρ : PBCatcher.Reflect.FormulaSat (encodeOpt inst) ρ) :
    hasPacking (inst.withBins
      (IndependentSet.countTrue (fun j => ρ (inst.numItems * inst.numBins + j))
        inst.numBins)) := by
  let y : Nat → Bool := fun j => ρ (inst.numItems * inst.numBins + j)
  have hcap : ∀ j, j < inst.numBins →
      sumIf inst.sizes (fun i => ρ (varIdx inst.numBins i j)) inst.numItems ≤
        inst.capacity * evalLit ρ (Literal.pos (inst.numItems * inst.numBins + j)) :=
    fun j hj => capOptConstr_load inst ρ j (hρ _ ((mem_encodeOpt inst _).2
      (Or.inr (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))))
  have hpick : ∀ i, ∃ j, i < inst.numItems →
      j < inst.numBins ∧ ρ (varIdx inst.numBins i j) = true := by
    intro i
    by_cases hi : i < inst.numItems
    · have ha := hρ _ ((mem_encodeOpt inst _).2
        (Or.inl (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))
      simp only [mkAssignConstr, varIdx, Constr.sat, OptCount.evalSum_posLits_shift] at ha
      obtain ⟨j, hj, hx⟩ := OptCount.countTrue_pos_exists
        (fun j => ρ (i * inst.numBins + j)) inst.numBins (by omega)
      exact ⟨j, fun _ => ⟨hj, hx⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  let pick : Nat → Nat := fun i => Classical.choose (hpick i)
  have hpick_spec : ∀ i, i < inst.numItems →
      pick i < inst.numBins ∧ ρ (varIdx inst.numBins i (pick i)) = true :=
    fun i => Classical.choose_spec (hpick i)
  -- the chosen bin of an item is used, since the item has positive size
  have hused : ∀ i, i < inst.numItems → y (pick i) = true := by
    intro i hi
    obtain ⟨hj, hx⟩ := hpick_spec i hi
    have hc := hcap (pick i) hj
    have hle := le_sumIf inst.sizes (fun i' => ρ (varIdx inst.numBins i' (pick i)))
      inst.numItems i hi hx
    have hp := hpos i hi
    show ρ (inst.numItems * inst.numBins + pick i) = true
    cases hy : ρ (inst.numItems * inst.numBins + pick i)
    · simp only [evalLit, hy] at hc; simp at hc; omega
    · rfl
  refine ⟨fun i => IndependentSet.countTrue y (pick i), ?_, ?_⟩
  · intro i hi
    exact OptCount.countTrue_lt_of_true y (hused i hi) (hpick_spec i hi).1
  · intro r _
    show binLoad inst.sizes _ r inst.numItems ≤ inst.capacity
    rw [binLoad_eq_sumIf]
    by_cases hex : ∃ i0, i0 < inst.numItems ∧ IndependentSet.countTrue y (pick i0) = r
    · obtain ⟨i0, hi0, hr⟩ := hex
      have hsub : sumIf inst.sizes
          (fun i => decide (IndependentSet.countTrue y (pick i) = r)) inst.numItems ≤
          sumIf inst.sizes (fun i => ρ (varIdx inst.numBins i (pick i0))) inst.numItems := by
        apply sumIf_mono
        intro i hi hd
        simp only [decide_eq_true_eq] at hd
        have hsame : pick i = pick i0 :=
          OptCount.countTrue_inj y (hused i hi) (hused i0 hi0) (by omega)
        rw [← hsame]
        exact (hpick_spec i hi).2
      have hc := hcap (pick i0) (hpick_spec i0 hi0).1
      have h1 := evalLit_le_one ρ (Literal.pos (inst.numItems * inst.numBins + pick i0))
      have h2 := Nat.mul_le_mul_left inst.capacity h1
      rw [Nat.mul_one] at h2
      omega
    · have hzero : sumIf inst.sizes
          (fun i => decide (IndependentSet.countTrue y (pick i) = r)) inst.numItems =
          sumIf inst.sizes (fun _ => false) inst.numItems :=
        sumIf_congr _ _ _ _ fun i hi => by
          simp only [decide_eq_false_iff_not]
          exact fun h => hex ⟨i, hi, h⟩
      rw [sumIf_false] at hzero
      omega

-- From a packing to a solution

/-- The valuation of a packing `assign` into `k'` bins: `x_{i,j}` iff
`assign i = j`, and `y_j` iff `j < k'`. -/
def binVal (n m k' : Nat) (assign : Nat → Nat) : Valuation := fun v =>
  if v < n * m then decide (assign (v / m) = v % m) else decide (v - n * m < k')

theorem binVal_x {n m k' i j : Nat} (assign : Nat → Nat) (hi : i < n) (hj : j < m) :
    binVal n m k' assign (varIdx m i j) = decide (assign i = j) := by
  simp only [binVal, if_pos (varIdx_lt hi hj), varIdx_div (by omega) hj,
    varIdx_mod (by omega) hj]

theorem binVal_y {n m k' : Nat} (assign : Nat → Nat) (j : Nat) :
    binVal n m k' assign (n * m + j) = decide (j < k') := by
  simp only [binVal, show ¬ n * m + j < n * m by omega, ↓reduceIte,
    show n * m + j - n * m = j by omega]

theorem binVal_sat (inst : Instance) (k' : Nat) (assign : Nat → Nat)
    (hpack : isValidPacking (inst.withBins k') assign) (hk : k' < inst.numBins) :
    PBCatcher.Reflect.FormulaSat (encodeOpt inst)
      (binVal inst.numItems inst.numBins k' assign) := by
  obtain ⟨hbin, hload⟩ := hpack
  have hbin : ∀ i, i < inst.numItems → assign i < k' := hbin
  have hload : ∀ j, j < k' → binLoad inst.sizes assign j inst.numItems ≤ inst.capacity :=
    hload
  intro c hc
  rcases (mem_encodeOpt inst c).1 hc with hc | hc
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    have hi := List.mem_range.1 hi
    have hai : assign i < inst.numBins := by have := hbin i hi; omega
    have hp := binVal_x (k' := k') assign hi hai
    simp only [decide_true] at hp
    simp only [mkAssignConstr, Constr.sat]
    simp only [varIdx] at hp ⊢
    rw [OptCount.evalSum_posLits_shift]
    have := OptCount.countTrue_lt_of_true
      (fun j => binVal inst.numItems inst.numBins k' assign (i * inst.numBins + j)) hp hai
    omega
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    have hj := List.mem_range.1 hj
    simp only [mkCapOptConstr, Constr.sat, evalSum_append, evalSum_neg_sumIf, evalSum,
      evalLit, binVal_y]
    have hcong : sumIf inst.sizes
        (fun i => !binVal inst.numItems inst.numBins k' assign (varIdx inst.numBins i j))
        inst.numItems = sumIf inst.sizes (fun i => !decide (assign i = j)) inst.numItems :=
      sumIf_congr _ _ _ _ fun i hi => by rw [binVal_x assign hi hj]
    have hcomp := sumIf_complement inst.sizes (fun i => decide (assign i = j)) inst.numItems
    have htot := totalSize_eq_sumAll_full inst
    rw [hcong]
    by_cases hjk : j < k'
    · have hl := hload j hjk
      rw [binLoad_eq_sumIf] at hl
      simp only [hjk, decide_true, ↓reduceIte]
      omega
    · have hzero : sumIf inst.sizes (fun i => decide (assign i = j)) inst.numItems =
          sumIf inst.sizes (fun _ => false) inst.numItems :=
        sumIf_congr _ _ _ _ fun i hi => by
          have := hbin i hi
          simp only [decide_eq_false_iff_not]
          omega
      rw [sumIf_false] at hzero
      simp only [hjk, decide_false, Bool.false_eq_true, ↓reduceIte]
      omega

/-- Bridge: the bounds `k ≤ Σ_j y_j ≤ k` with `m` bins available give the
minimum number of bins `k` (positive sizes). The lower bound covers only
packings into fewer than `m` bins; the solution of the upper bound shows
`k ≤ m`, which covers the rest. -/
theorem minBins_of_bounds (inst : Instance) (k : Nat) (hpos : sizesPositive inst = true)
    (h : PBCatcher.Reflect.formulaBounds (encodeOpt inst) (binObjective inst) 0
      (some (k : Int)) (some (k : Int))) :
    minBins inst k := by
  have hpos := sizesPositive_spec inst hpos
  obtain ⟨hlb, hub⟩ := h
  obtain ⟨ρ, hρ, hval⟩ := hub
  have hv : PBCatcher.Reflect.opbVal (binObjective inst) 0 ρ ≤ (k : Int) := hval
  rw [binObjective_opbVal] at hv
  have hv2 : (k : Int) ≤ PBCatcher.Reflect.opbVal (binObjective inst) 0 ρ := hlb ρ hρ
  rw [binObjective_opbVal] at hv2
  have hle := OptCount.countTrue_le
    (fun j => ρ (inst.numItems * inst.numBins + j)) inst.numBins
  refine ⟨?_, ?_⟩
  · obtain ⟨assign, hbin, hload⟩ := packing_of_sat inst hpos ρ hρ
    refine ⟨assign, fun i hi => ?_, fun j hj => hload j (by
      simp only [Instance.withBins] at hj ⊢; omega)⟩
    have : assign i < IndependentSet.countTrue
        (fun j => ρ (inst.numItems * inst.numBins + j)) inst.numBins := hbin i hi
    show assign i < k
    omega
  · intro k' ⟨assign, hpack⟩
    rcases Nat.lt_or_ge k' inst.numBins with hk | hk
    · have hs := binVal_sat inst k' assign hpack hk
      have hl : (k : Int) ≤ PBCatcher.Reflect.opbVal (binObjective inst) 0
          (binVal inst.numItems inst.numBins k' assign) := hlb _ hs
      rw [binObjective_opbVal] at hl
      have hcount : IndependentSet.countTrue
          (fun j => binVal inst.numItems inst.numBins k' assign
            (inst.numItems * inst.numBins + j)) inst.numBins =
          IndependentSet.countTrue (fun j => decide (j < k')) inst.numBins := by
        simp only [binVal_y]
      rw [hcount, OptCount.countTrue_lt_const] at hl
      omega
    · omega

/-- `binpack_opt_reflect name inst k "proof.pbp"`: `k` is the minimum number
of bins, from one VeriPB optimization proof of `min: Σ_j y_j` over the
`inst.numBins`-bin encoding `encodeOpt` (`conclusion BOUNDS k : id k :
solution`), by native evaluation of `checkProofClaimBool`;
`sizesPositive inst` is checked by `decide`. This records a per-use axiom
`checkProofClaimBool ... = true` (`_native.binpack_opt_reflect.ax_*`, the
same mechanism as `native_decide`; see `mkFormulaUnsatProof`). -/
elab "binpack_opt_reflect " nm:ident ppSpace instTerm:term:max ppSpace kTerm:num
    ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let proofPath := proofFile.getString
  liftTermElabM do
    let instExpr ← Lean.Elab.Term.elabTerm instTerm (some (mkConst ``Instance))
    let instExpr ← instantiateMVars instExpr
    let k := kTerm.getNat
    let kVal := mkRawNatLit k
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath)
    let constrsExpr := mkApp (mkConst ``encodeOpt) instExpr
    let numVarsExpr := mkApp (mkConst ``Instance.numVarsOpt) instExpr
    let objExpr := mkApp (mkConst ``binObjective) instExpr
    let offsetExpr := toExpr (0 : Int)
    let hposVal ← whnfD (mkApp (mkConst ``sizesPositive) instExpr)
    unless hposVal.isConstOf ``Bool.true do
      throwError "binpack_opt_reflect: every item size must be positive"
    let claim := PBCatcher.Reflect.Claim.bounds (some (k : Int)) (some (k : Int))
    let boundsProof ← PBCatcher.Reflect.mkClaimProof `binpack_opt_reflect
      constrsExpr numVarsExpr objExpr offsetExpr proofStr claim
      (ref? := some (← getRef))
    let hposType := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Bool)
      (mkApp (mkConst ``sizesPositive) instExpr) (mkConst ``Bool.true)
    let hposProof ← mkDecideProof hposType
    let finalProof := mkApp4 (mkConst ``minBins_of_bounds) instExpr kVal hposProof
      boundsProof
    let finalType := mkApp2 (mkConst ``minBins) instExpr kVal
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : minBins inst {k} (reflection)"

/-- The bp12 items with 6 bins available. -/
def inst12_m6 : Instance := { inst12_5 with numBins := 6 }

/-- The bp12 items with 7 bins available. -/
def inst12_m7 : Instance := { inst12_5 with numBins := 7 }

-- The 12 items need 6 bins of capacity 14 (proof with 6 bins available).
binpack_opt_reflect bp12_m6_minBins inst12_m6 6
  "applications/binpack/bp12_m6_opt_kernel.pbp"
-- The same optimum from the proof with 7 bins available.
binpack_opt_reflect bp12_m7_minBins inst12_m7 6
  "applications/binpack/bp12_m7_opt_kernel.pbp"

-- `minBins` ignores `numBins`: both proofs speak about the same items.
example : minBins inst12_5 6 := bp12_m6_minBins
example : minBins inst12_5 6 := bp12_m7_minBins

end BinPacking
