/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import PBCatcher.PseudoBoolean

/-!
# Dominance: order semantics and abstract soundness

Semantic objects and abstract soundness theorems for the VeriPB dominance rule (Bogaerts,
Gocht, McCreesh, Nordström, JAIR 2023; orders with auxiliary variables as in CakePB).
Nothing here refers to the checker state;
the checker instantiates the lists of constraints with the core and the database.

## Main definitions

* `OrderData` — an order encoding: left, right and auxiliary variables, `spec` and `defs`
* `OrderData.Rel` — the induced relation on keys (bit vectors)
* `Leq O z` — the loaded preorder on valuations, through the key of the literals `z`
* `IsSpec`, `GoodOrder` — spec validity and the stored-order invariant
* `CoreValid` — every core model has a database counterpart below it in the order

## Main results

* `exists_minimal` (T2) — minimal elements w.r.t. a transitive relation on keys
* `coreValid_dom` (T3), `coreValid_red` (T4), `coreValid_delc` (T5)
* `refl_of_goals`, `trans_of_goals`, `ordLeq_of_goal`, `ordStrict_of_goal`, `specElim_leq`,
  `specElim_geq`, `key_applyValuation_of_untouched`, `spec_valid` (T7)
-/

namespace Sat.PB.Dominance

/-! ## Variables of a constraint, agreement -/

/-- The variables of the terms of a constraint (with repetitions). -/
def varsOf (c : Constr) : List Nat := c.terms.map (fun t => t.2.var)

theorem evalLit_congr {ρ ρ' : Valuation} {l : Literal} (h : ρ l.var = ρ' l.var) :
    evalLit ρ l = evalLit ρ' l := by
  cases l <;> simp only [Literal.var] at h <;> simp only [evalLit, h]

theorem evalSum_congr {ρ ρ' : Valuation} : ∀ {ts : List Term},
    (∀ t ∈ ts, ρ t.2.var = ρ' t.2.var) → evalSum ρ ts = evalSum ρ' ts
  | [], _ => rfl
  | (a, l) :: rest, h => by
    simp only [evalSum]
    rw [evalLit_congr (h (a, l) List.mem_cons_self),
      evalSum_congr (fun t ht => h t (List.mem_cons_of_mem _ ht))]

/-- Satisfaction depends only on the variables of the constraint. -/
theorem sat_of_agree {c : Constr} {ρ ρ' : Valuation}
    (h : ∀ x ∈ varsOf c, ρ x = ρ' x) : c.sat ρ ↔ c.sat ρ' := by
  unfold Constr.sat
  rw [evalSum_congr (ts := c.terms) (fun t ht => h _ (List.mem_map_of_mem ht))]

/-- List form of `sat_of_agree`: valuations agreeing on `V` satisfy the same constraints
over `V`. -/
theorem sat_list_of_agree {cs : List Constr} {V : List Nat} {ρ ρ' : Valuation}
    (hv : ∀ c ∈ cs, ∀ x ∈ varsOf c, x ∈ V) (h : ∀ x ∈ V, ρ x = ρ' x)
    (hs : ∀ c ∈ cs, c.sat ρ) : ∀ c ∈ cs, c.sat ρ' :=
  fun c hc => (sat_of_agree (fun x hx => h x (hv c hc x hx))).mp (hs c hc)

/-! ## Literal values, keys -/

/-- Boolean value of a literal. -/
def litBool (ρ : Valuation) : Literal → Bool
  | .pos i => ρ i
  | .neg i => !(ρ i)

theorem evalLit_eq_litBool (ρ : Valuation) (l : Literal) :
    evalLit ρ l = if litBool ρ l then 1 else 0 := by
  cases l with
  | pos i => cases h : ρ i <;> simp [evalLit, litBool, h]
  | neg i => cases h : ρ i <;> simp [evalLit, litBool, h]

/-- The key of a valuation: the values of the loaded literals `z`. -/
def key (z : List Literal) (ρ : Valuation) : List Bool := z.map (litBool ρ)

@[simp] theorem key_length (z : List Literal) (ρ : Valuation) : (key z ρ).length = z.length :=
  List.length_map ..

/-! ## Pasting -/

/-- `paste A η ρ` takes the values of `η` on `A` and of `ρ` elsewhere. -/
def paste (A : List Nat) (η ρ : Valuation) : Valuation := fun x => if x ∈ A then η x else ρ x

theorem paste_of_not_mem {A : List Nat} {η ρ : Valuation} {x : Nat} (h : x ∉ A) :
    paste A η ρ x = ρ x := by simp [paste, h]

theorem paste_of_mem {A : List Nat} {η ρ : Valuation} {x : Nat} (h : x ∈ A) :
    paste A η ρ x = η x := by simp [paste, h]

/-- Pasting values on `A` keeps the satisfaction of a constraint without variables in `A`. -/
theorem paste_sat {A : List Nat} {η ρ : Valuation} {c : Constr}
    (h : ∀ x ∈ varsOf c, x ∉ A) : c.sat (paste A η ρ) ↔ c.sat ρ :=
  sat_of_agree (fun x hx => paste_of_not_mem (h x hx))

/-! ## Substitution values -/

/-- Value of a substitution entry under `ρ` (what `applyValuation` computes). -/
def svEval (ρ : Valuation) : SubstVal → Bool
  | .zero => false
  | .one => true
  | .posLit j => ρ j
  | .negLit j => !(ρ j)

/-- Variables of a substitution entry. -/
def svVars : SubstVal → List Nat
  | .posLit j => [j]
  | .negLit j => [j]
  | _ => []

/-- Negated substitution entry. -/
def svFlip : SubstVal → SubstVal
  | .zero => .one
  | .one => .zero
  | .posLit j => .negLit j
  | .negLit j => .posLit j

theorem svEval_congr {ρ ρ' : Valuation} {sv : SubstVal} (h : ∀ j ∈ svVars sv, ρ j = ρ' j) :
    svEval ρ sv = svEval ρ' sv := by
  cases sv <;> simp_all [svEval, svVars]

theorem svEval_flip (ρ : Valuation) (sv : SubstVal) : svEval ρ (svFlip sv) = !(svEval ρ sv) := by
  cases sv <;> simp [svFlip, svEval]

theorem svVars_flip (sv : SubstVal) : svVars (svFlip sv) = svVars sv := by
  cases sv <;> rfl

theorem applyValuation_eq (ω : List (Nat × SubstVal)) (ρ : Valuation) (x : Nat) :
    applyValuation ω ρ x =
      match lookupSubst ω x with
      | none => ρ x
      | some sv => svEval ρ sv := by
  simp only [applyValuation]
  cases lookupSubst ω x with
  | none => rfl
  | some sv => cases sv <;> rfl

/-- A literal as a substitution entry. -/
def litSV : Literal → SubstVal
  | .pos i => .posLit i
  | .neg i => .negLit i

theorem svEval_litSV (ρ : Valuation) (l : Literal) : svEval ρ (litSV l) = litBool ρ l := by
  cases l <;> rfl

theorem svVars_litSV (l : Literal) : svVars (litSV l) = [l.var] := by
  cases l <;> rfl

/-- The literal `l` pushed through the witness `ω` (design: `ω̂(l)`). -/
def litSubst (ω : List (Nat × SubstVal)) (l : Literal) : SubstVal :=
  match lookupSubst ω l.var with
  | none => litSV l
  | some sv =>
    match l with
    | .pos _ => sv
    | .neg _ => svFlip sv

theorem svEval_litSubst (ω : List (Nat × SubstVal)) (ρ : Valuation) (l : Literal) :
    svEval ρ (litSubst ω l) = litBool (applyValuation ω ρ) l := by
  cases l with
  | pos i =>
    simp only [litSubst, Literal.var, litBool, applyValuation_eq]
    cases lookupSubst ω i with
    | none => rfl
    | some sv => rfl
  | neg i =>
    simp only [litSubst, Literal.var, litBool, applyValuation_eq]
    cases lookupSubst ω i with
    | none => rfl
    | some sv => exact svEval_flip ρ sv

/-- The image of `ω` at `x` contains no variable of `A`. -/
def ImgFree (ω : List (Nat × SubstVal)) (A : List Nat) (x : Nat) : Prop :=
  ∀ sv, lookupSubst ω x = some sv → ∀ j ∈ svVars sv, j ∉ A

theorem litSubst_vars_free {ω : List (Nat × SubstVal)} {A : List Nat} {l : Literal}
    (h1 : l.var ∉ A) (h2 : ImgFree ω A l.var) : ∀ j ∈ svVars (litSubst ω l), j ∉ A := by
  intro j hj
  unfold litSubst at hj
  revert hj
  cases hl : lookupSubst ω l.var with
  | none =>
    intro hj
    simp only [svVars_litSV, List.mem_singleton] at hj
    exact hj ▸ h1
  | some sv =>
    cases l with
    | pos i => intro hj; exact h2 sv hl j hj
    | neg i =>
      intro hj
      simp only [svVars_flip] at hj
      exact h2 sv hl j hj

theorem map_svEval_congr {X : List SubstVal} {ρ ρ' : Valuation}
    (h : ∀ sv ∈ X, ∀ j ∈ svVars sv, ρ j = ρ' j) : X.map (svEval ρ) = X.map (svEval ρ') :=
  List.map_congr_left (fun sv hsv => svEval_congr (h sv hsv))

theorem key_eq_map_litSV (z : List Literal) (ρ : Valuation) :
    key z ρ = (z.map litSV).map (svEval ρ) := by
  simp only [key, List.map_map]
  exact List.map_congr_left (fun l _ => (svEval_litSV ρ l).symm)

theorem key_comp_eq_map_litSubst (z : List Literal) (ω : List (Nat × SubstVal))
    (ρ : Valuation) : key z (applyValuation ω ρ) = (z.map (litSubst ω)).map (svEval ρ) := by
  simp only [key, List.map_map]
  exact List.map_congr_left (fun l _ => (svEval_litSubst ω ρ l).symm)

/-- T1: pasting on `A` keeps the key when no loaded literal is over `A`. -/
theorem key_paste {A : List Nat} {η ρ : Valuation} {z : List Literal}
    (hz : ∀ l ∈ z, l.var ∉ A) : key z (paste A η ρ) = key z ρ := by
  rw [key_eq_map_litSV, key_eq_map_litSV]
  apply map_svEval_congr
  intro sv hsv j hj
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hsv
  rw [svVars_litSV, List.mem_singleton] at hj
  exact paste_of_not_mem (hj ▸ hz l hl)

/-- T1: pasting on `A` keeps the key of the substituted valuation when additionally the
image of `ω` on the variables of `z` avoids `A`. -/
theorem key_paste_comp {A : List Nat} {η ρ : Valuation} {z : List Literal}
    {ω : List (Nat × SubstVal)} (hz : ∀ l ∈ z, l.var ∉ A)
    (himg : ∀ l ∈ z, ImgFree ω A l.var) :
    key z (applyValuation ω (paste A η ρ)) = key z (applyValuation ω ρ) := by
  rw [key_comp_eq_map_litSubst, key_comp_eq_map_litSubst]
  apply map_svEval_congr
  intro sv hsv j hj
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hsv
  exact paste_of_not_mem (litSubst_vars_free (hz l hl) (himg l hl) j hj)

/-! ## Orders -/

/-- An order encoding: `left`, `right`, `aux` variables and the `spec`/`defs` constraints. -/
structure OrderData where
  left : List Nat
  right : List Nat
  aux : List Nat
  spec : List Constr
  defs : List Constr
  deriving Repr, Inhabited

/-- `ρ` is a model of the order encoding at keys `p` (left) and `q` (right). The key
lengths are forced by the map equations. -/
def OrderData.models (O : OrderData) (p q : List Bool) (ρ : Valuation) : Prop :=
  O.left.map ρ = p ∧ O.right.map ρ = q ∧ ∀ c ∈ O.spec ++ O.defs, c.sat ρ

theorem OrderData.models_length {O : OrderData} {p q : List Bool} {ρ : Valuation}
    (h : O.models p q ρ) : p.length = O.left.length ∧ q.length = O.right.length := by
  obtain ⟨h1, h2, _⟩ := h
  subst h1; subst h2
  exact ⟨List.length_map .., List.length_map ..⟩

/-- The relation on keys induced by an order encoding (aux values existential). -/
def OrderData.Rel (O : OrderData) (p q : List Bool) : Prop := ∃ ρ, O.models p q ρ

/-- The loaded preorder on valuations. -/
def Leq (O : OrderData) (z : List Literal) (α β : Valuation) : Prop :=
  O.Rel (key z α) (key z β)

/-- Spec validity: aux values satisfying `spec` exist for every valuation. -/
def IsSpec (O : OrderData) : Prop :=
  ∀ ρ : Valuation, ∃ ρ' : Valuation, (∀ x, x ∉ O.aux → ρ' x = ρ x) ∧ ∀ c ∈ O.spec, c.sat ρ'

/-- The invariant of a stored order. -/
structure GoodOrder (O : OrderData) : Prop where
  wf : O.left.length = O.right.length ∧ (O.left ++ O.right ++ O.aux).Nodup
  vars : ∀ c ∈ O.spec ++ O.defs, ∀ x ∈ varsOf c, x ∈ O.left ++ O.right ++ O.aux
  isSpec : IsSpec O
  refl : ∀ p, p.length = O.left.length → O.Rel p p
  trans : ∀ p q r, O.Rel p q → O.Rel q r → O.Rel p r

/-! ## T2: minimal elements -/

/-- All Boolean lists of length `n`. -/
private def allKeys : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allKeys n).map (true :: ·) ++ (allKeys n).map (false :: ·)

private theorem mem_allKeys : ∀ {n : Nat} (k : List Bool), k.length = n → k ∈ allKeys n
  | 0, [], _ => by simp [allKeys]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h
  | n + 1, b :: k, h => by
    have hk : k ∈ allKeys n := mem_allKeys k (by simpa using h)
    cases b
    · exact List.mem_append_right _ (List.mem_map_of_mem hk)
    · exact List.mem_append_left _ (List.mem_map_of_mem hk)

/-- Strict `countP` monotonicity: pointwise implication plus one witness. -/
private theorem countP_lt_of_witness {α : Type} {p q : α → Bool} : ∀ {l : List α},
    (∀ x ∈ l, p x = true → q x = true) → (∃ x ∈ l, q x = true ∧ p x = false) →
    l.countP p < l.countP q
  | [], _, ⟨_, hx, _⟩ => by simp at hx
  | a :: l, hpq, ⟨x, hx, hqx, hpx⟩ => by
    rw [List.countP_cons, List.countP_cons]
    have hpq' : ∀ y ∈ l, p y = true → q y = true :=
      fun y hy => hpq y (List.mem_cons_of_mem _ hy)
    have hmono : l.countP p ≤ l.countP q := List.countP_mono_left hpq'
    have ha : (if p a = true then 1 else 0) ≤ (if q a = true then 1 else 0) := by
      cases hp : p a
      · simp
      · simp [hpq a List.mem_cons_self hp]
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp only [hqx, hpx]
      simp only [Bool.false_eq_true, if_false, if_true]
      omega
    · have ih := countP_lt_of_witness hpq' ⟨x, hx', hqx, hpx⟩
      omega

open Classical in
/-- Number of keys of length `n` strictly below `k`. -/
private noncomputable def belowCount (R : List Bool → List Bool → Prop) (n : Nat) (k : List Bool) :
    Nat :=
  (allKeys n).countP (fun κ => decide (R κ k ∧ ¬ R k κ))

/-- A strictly smaller key has a smaller `belowCount` (transitivity only). -/
private theorem belowCount_lt {R : List Bool → List Bool → Prop}
    (htrans : ∀ a b c, R a b → R b c → R a c) {n : Nat} {k k' : List Bool}
    (hk' : k'.length = n) (h1 : R k' k) (h2 : ¬ R k k') :
    belowCount R n k' < belowCount R n k := by
  unfold belowCount
  apply countP_lt_of_witness
  · intro κ _ hκ
    simp only [decide_eq_true_eq] at hκ ⊢
    exact ⟨htrans _ _ _ hκ.1 h1, fun h => h2 (htrans _ _ _ h hκ.1)⟩
  · refine ⟨k', mem_allKeys k' hk', ?_, ?_⟩
    · simp only [decide_eq_true_eq]; exact ⟨h1, h2⟩
    · simp only [decide_eq_false_iff_not]; exact fun h => h.2 h.1

/-- T2: a nonempty set of valuations has an element that is minimal w.r.t. a transitive
relation on keys of fixed length. Reflexivity is not used. -/
theorem exists_minimal {R : List Bool → List Bool → Prop}
    (htrans : ∀ a b c, R a b → R b c → R a c) {n : Nat} (kf : Valuation → List Bool)
    (hk : ∀ α, (kf α).length = n) (S : Valuation → Prop) (hS : ∃ α, S α) :
    ∃ α, S α ∧ ∀ β, S β → R (kf β) (kf α) → R (kf α) (kf β) := by
  have main : ∀ m, ∀ α, S α → belowCount R n (kf α) ≤ m →
      ∃ α, S α ∧ ∀ β, S β → R (kf β) (kf α) → R (kf α) (kf β) := by
    intro m
    induction m with
    | zero =>
      intro α hα hμ
      refine ⟨α, hα, fun β _ h1 => Classical.byContradiction fun h2 => ?_⟩
      have := belowCount_lt htrans (hk β) h1 h2
      omega
    | succ m ih =>
      intro α hα hμ
      apply Classical.byContradiction
      intro hno
      apply hno
      refine ⟨α, hα, fun β hβ h1 => Classical.byContradiction fun h2 => ?_⟩
      have := belowCount_lt htrans (hk β) h1 h2
      exact hno (ih β hβ (by omega))
  obtain ⟨α, hα⟩ := hS
  exact main _ α hα (Nat.le_refl _)

/-! ## CoreValid and its preservation (T3, T4, T5) -/

/-- Every model of the core `C` has a counterpart satisfying the database `B` that is below
it in the loaded order and not worse in the objective `f`. -/
def CoreValid (O : OrderData) (z : List Literal) (C B : List Constr)
    (f : Valuation → Int) : Prop :=
  ∀ ρ, (∀ c ∈ C, c.sat ρ) → ∃ ρ', (∀ c ∈ B, c.sat ρ') ∧ Leq O z ρ' ρ ∧ f ρ' ≤ f ρ

theorem leq_trans {O : OrderData} {z : List Literal}
    (htrans : ∀ p q r, O.Rel p q → O.Rel q r → O.Rel p r) {α β γ : Valuation}
    (h1 : Leq O z α β) (h2 : Leq O z β γ) : Leq O z α γ :=
  htrans _ _ _ h1 h2

theorem leq_refl {O : OrderData} {z : List Literal}
    (hrefl : ∀ p, p.length = O.left.length → O.Rel p p) (hz : z.length = O.left.length)
    (ρ : Valuation) : Leq O z ρ ρ :=
  hrefl _ (by rw [key_length, hz])

/-- T3: the dominance rule preserves `CoreValid` (the new constraint `c` joins the
database). Only transitivity of the order is used. -/
theorem coreValid_dom {O : OrderData} {z : List Literal} {C B : List Constr}
    {f : Valuation → Int} {c : Constr} {ω : List (Nat × SubstVal)}
    (htrans : ∀ p q r, O.Rel p q → O.Rel q r → O.Rel p r)
    (hcv : CoreValid O z C B f)
    (hgoals : ∀ ρ, (∀ d ∈ B, d.sat ρ) → ¬ c.sat ρ →
      (∀ d ∈ C, d.sat (applyValuation ω ρ)) ∧ Leq O z (applyValuation ω ρ) ρ ∧
      ¬ Leq O z ρ (applyValuation ω ρ) ∧ f (applyValuation ω ρ) ≤ f ρ) :
    CoreValid O z C (c :: B) f := by
  intro ρ hρ
  apply Classical.byContradiction
  intro hno
  let S : Valuation → Prop := fun α => (∀ d ∈ C, d.sat α) ∧
    ¬ ∃ α', (∀ d ∈ c :: B, d.sat α') ∧ Leq O z α' α ∧ f α' ≤ f α
  obtain ⟨α, ⟨hαC, hαno⟩, hmin⟩ := exists_minimal (R := O.Rel) htrans (n := z.length)
    (key z) (fun α => key_length z α) S ⟨ρ, hρ, hno⟩
  obtain ⟨α₁, hα₁B, hα₁le, hα₁f⟩ := hcv α hαC
  have hα₁c : ¬ c.sat α₁ := fun h =>
    hαno ⟨α₁, List.forall_mem_cons.mpr ⟨h, hα₁B⟩, hα₁le, hα₁f⟩
  obtain ⟨g1, g2, g3, g4⟩ := hgoals α₁ hα₁B hα₁c
  have h2le : Leq O z (applyValuation ω α₁) α := leq_trans htrans g2 hα₁le
  have h2nle : ¬ Leq O z α (applyValuation ω α₁) := fun h => g3 (leq_trans htrans hα₁le h)
  rcases Classical.em (S (applyValuation ω α₁)) with hS | hS
  · exact h2nle (hmin _ hS h2le)
  · have hex : ∃ α', (∀ d ∈ c :: B, d.sat α') ∧ Leq O z α' (applyValuation ω α₁) ∧
        f α' ≤ f (applyValuation ω α₁) :=
      Classical.byContradiction fun hne => hS ⟨g1, hne⟩
    obtain ⟨α', hα'B, hα'le, hα'f⟩ := hex
    exact hαno ⟨α', hα'B, leq_trans htrans hα'le h2le,
      Int.le_trans hα'f (Int.le_trans g4 hα₁f)⟩

/-- Restricting the core keeps `CoreValid` (models of the larger core are models of the
smaller one). -/
theorem coreValid_mono_C {O : OrderData} {z : List Literal} {C C' B : List Constr}
    {f : Valuation → Int} (hcv : CoreValid O z C B f) (hsub : ∀ c ∈ C, c ∈ C') :
    CoreValid O z C' B f :=
  fun ρ hρ => hcv ρ (fun c hc => hρ c (hsub c hc))

/-- Shrinking the database keeps `CoreValid`. -/
theorem coreValid_mono_B {O : OrderData} {z : List Literal} {C B B' : List Constr}
    {f : Valuation → Int} (hsub : ∀ c ∈ B', c ∈ B) (hcv : CoreValid O z C B f) :
    CoreValid O z C B' f := by
  intro ρ hρ
  obtain ⟨ρ', h1, h2, h3⟩ := hcv ρ hρ
  exact ⟨ρ', fun c hc => h1 c (hsub c hc), h2, h3⟩

/-- T3, core version: the dominance result goes to the core and the database. -/
theorem coreValid_dom_core {O : OrderData} {z : List Literal} {C B : List Constr}
    {f : Valuation → Int} {c : Constr} {ω : List (Nat × SubstVal)}
    (htrans : ∀ p q r, O.Rel p q → O.Rel q r → O.Rel p r)
    (hcv : CoreValid O z C B f)
    (hgoals : ∀ ρ, (∀ d ∈ B, d.sat ρ) → ¬ c.sat ρ →
      (∀ d ∈ C, d.sat (applyValuation ω ρ)) ∧ Leq O z (applyValuation ω ρ) ρ ∧
      ¬ Leq O z ρ (applyValuation ω ρ) ∧ f (applyValuation ω ρ) ≤ f ρ) :
    CoreValid O z (c :: C) (c :: B) f :=
  coreValid_mono_C (coreValid_dom htrans hcv hgoals)
    (fun _ hd => List.mem_cons_of_mem _ hd)

/-- T4: the redundance rule preserves `CoreValid`. -/
theorem coreValid_red {O : OrderData} {z : List Literal} {C B : List Constr}
    {f : Valuation → Int} {c : Constr} {ω : List (Nat × SubstVal)}
    (htrans : ∀ p q r, O.Rel p q → O.Rel q r → O.Rel p r)
    (hcv : CoreValid O z C B f)
    (hgoals : ∀ ρ, (∀ d ∈ B, d.sat ρ) → ¬ c.sat ρ →
      (∀ d ∈ c :: B, d.sat (applyValuation ω ρ)) ∧ Leq O z (applyValuation ω ρ) ρ ∧
      f (applyValuation ω ρ) ≤ f ρ) :
    CoreValid O z C (c :: B) f := by
  intro ρ hρ
  obtain ⟨ρ₁, h1B, h1le, h1f⟩ := hcv ρ hρ
  rcases Classical.em (c.sat ρ₁) with hc | hc
  · exact ⟨ρ₁, List.forall_mem_cons.mpr ⟨hc, h1B⟩, h1le, h1f⟩
  · obtain ⟨g1, g2, g4⟩ := hgoals ρ₁ h1B hc
    exact ⟨_, g1, leq_trans htrans g2 h1le, Int.le_trans g4 h1f⟩

/-- T4, core version. -/
theorem coreValid_red_core {O : OrderData} {z : List Literal} {C B : List Constr}
    {f : Valuation → Int} {c : Constr} {ω : List (Nat × SubstVal)}
    (htrans : ∀ p q r, O.Rel p q → O.Rel q r → O.Rel p r)
    (hcv : CoreValid O z C B f)
    (hgoals : ∀ ρ, (∀ d ∈ B, d.sat ρ) → ¬ c.sat ρ →
      (∀ d ∈ c :: B, d.sat (applyValuation ω ρ)) ∧ Leq O z (applyValuation ω ρ) ρ ∧
      f (applyValuation ω ρ) ≤ f ρ) :
    CoreValid O z (c :: C) (c :: B) f :=
  coreValid_mono_C (coreValid_red htrans hcv hgoals) (fun _ hd => List.mem_cons_of_mem _ hd)

/-- T4 under strengthening-to-core: the goals cover only `c` and the core; `himpl`
(every core model is a database model) supplies the rest. -/
theorem coreValid_red_s2c {O : OrderData} {z : List Literal} {C B : List Constr}
    {f : Valuation → Int} {c : Constr} {ω : List (Nat × SubstVal)}
    (htrans : ∀ p q r, O.Rel p q → O.Rel q r → O.Rel p r)
    (hcv : CoreValid O z C B f)
    (himpl : ∀ ρ, (∀ d ∈ C, d.sat ρ) → ∀ d ∈ B, d.sat ρ)
    (hgoals : ∀ ρ, (∀ d ∈ B, d.sat ρ) → ¬ c.sat ρ →
      (∀ d ∈ c :: C, d.sat (applyValuation ω ρ)) ∧ Leq O z (applyValuation ω ρ) ρ ∧
      f (applyValuation ω ρ) ≤ f ρ) :
    CoreValid O z C (c :: B) f := by
  apply coreValid_red htrans hcv
  intro ρ hρ hc
  obtain ⟨g1, g2, g4⟩ := hgoals ρ hρ hc
  obtain ⟨g1c, g1C⟩ := List.forall_mem_cons.mp g1
  exact ⟨List.forall_mem_cons.mpr ⟨g1c, himpl _ g1C⟩, g2, g4⟩

/-- T5: checked deletion of the core constraint `E` preserves `CoreValid` (the database is
unchanged here; deleting `E` from it is `coreValid_mono_B`). -/
theorem coreValid_delc {O : OrderData} {z : List Literal} {C' B : List Constr}
    {f : Valuation → Int} {E : Constr} {ω : List (Nat × SubstVal)}
    (htrans : ∀ p q r, O.Rel p q → O.Rel q r → O.Rel p r)
    (hcv : CoreValid O z (E :: C') B f)
    (hgoals : ∀ ρ, (∀ d ∈ C', d.sat ρ) → ¬ E.sat ρ →
      (∀ d ∈ E :: C', d.sat (applyValuation ω ρ)) ∧ Leq O z (applyValuation ω ρ) ρ ∧
      f (applyValuation ω ρ) ≤ f ρ) :
    CoreValid O z C' B f := by
  intro ρ hρ
  rcases Classical.em (E.sat ρ) with hE | hE
  · exact hcv ρ (List.forall_mem_cons.mpr ⟨hE, hρ⟩)
  · obtain ⟨g1, g2, g4⟩ := hgoals ρ hρ hE
    obtain ⟨ρ', h'B, h'le, h'f⟩ := hcv _ g1
    exact ⟨ρ', h'B, leq_trans htrans h'le g2, Int.le_trans h'f g4⟩

/-- `load_order`: reflexivity gives `CoreValid` with the identity counterpart. -/
theorem coreValid_refl {O : OrderData} {z : List Literal} {C : List Constr}
    {f : Valuation → Int}
    (hrefl : ∀ p, p.length = O.left.length → O.Rel p p) (hz : z.length = O.left.length) :
    CoreValid O z C C f :=
  fun ρ hρ => ⟨ρ, hρ, leq_refl hrefl hz ρ, Int.le_refl _⟩

/-- An implied constraint joins the database. -/
theorem coreValid_cons_implied {O : OrderData} {z : List Literal} {C B : List Constr}
    {f : Valuation → Int} {c : Constr}
    (himp : ∀ ρ, (∀ d ∈ B, d.sat ρ) → c.sat ρ) (hcv : CoreValid O z C B f) :
    CoreValid O z C (c :: B) f := by
  intro ρ hρ
  obtain ⟨ρ', h1, h2, h3⟩ := hcv ρ hρ
  exact ⟨ρ', List.forall_mem_cons.mpr ⟨himp ρ' h1, h1⟩, h2, h3⟩

/-- `obju`: an objective equal to the old one on core models (needs `C ⊆ B`). -/
theorem coreValid_obj_eq {O : OrderData} {z : List Literal} {C B : List Constr}
    {f f' : Valuation → Int} (hCB : ∀ c ∈ C, c ∈ B)
    (heq : ∀ ρ, (∀ d ∈ C, d.sat ρ) → f' ρ = f ρ) (hcv : CoreValid O z C B f) :
    CoreValid O z C B f' := by
  intro ρ hρ
  obtain ⟨ρ', h1, h2, h3⟩ := hcv ρ hρ
  have hρ'C : ∀ d ∈ C, d.sat ρ' := fun d hd => h1 d (hCB d hd)
  refine ⟨ρ', h1, h2, ?_⟩
  rw [heq ρ hρ, heq ρ' hρ'C]
  exact h3

/-- `soli`/`obji`: a constraint closed downwards under `f` joins core and database. -/
theorem coreValid_cons_bound {O : OrderData} {z : List Literal} {C B : List Constr}
    {f : Valuation → Int} {h : Constr}
    (hdown : ∀ ρ ρ', f ρ' ≤ f ρ → h.sat ρ → h.sat ρ') (hcv : CoreValid O z C B f) :
    CoreValid O z (h :: C) (h :: B) f := by
  intro ρ hρ
  obtain ⟨hh, hC⟩ := List.forall_mem_cons.mp hρ
  obtain ⟨ρ', h1, h2, h3⟩ := hcv ρ hC
  exact ⟨ρ', List.forall_mem_cons.mpr ⟨hdown ρ ρ' h3 hh, h1⟩, h2, h3⟩

/-! ## Substitution infrastructure for the order lemmas -/

theorem lookupSubst_cons_self (x : Nat) (sv : SubstVal) (s : List (Nat × SubstVal)) :
    lookupSubst ((x, sv) :: s) x = some sv := by
  simp [lookupSubst]

theorem lookupSubst_cons_ne {x y : Nat} (sv : SubstVal) (s : List (Nat × SubstVal))
    (h : y ≠ x) : lookupSubst ((y, sv) :: s) x = lookupSubst s x := by
  simp [lookupSubst, h]

theorem lookupSubst_none_of_not_key {s : List (Nat × SubstVal)} {x : Nat}
    (h : ∀ p ∈ s, p.1 ≠ x) : lookupSubst s x = none := by
  induction s with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨y, sv⟩ := hd
    rw [lookupSubst_cons_ne _ _ (h (y, sv) List.mem_cons_self)]
    exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem lookupSubst_zip_none : ∀ {k : List Nat} {v : List SubstVal} {x : Nat},
    x ∉ k → lookupSubst (k.zip v) x = none
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | y :: k, sv :: v, x, hx => by
    rw [List.zip_cons_cons, lookupSubst_cons_ne _ _ (fun h => hx (by subst h; exact List.mem_cons_self))]
    exact lookupSubst_zip_none (fun h => hx (List.mem_cons_of_mem _ h))

theorem map_applyValuation_zip {ρ : Valuation} : ∀ {k : List Nat} {v : List SubstVal},
    k.Nodup → k.length = v.length → k.map (applyValuation (k.zip v) ρ) = v.map (svEval ρ)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: k, sv :: v, hnd, hlen => by
    have hx : x ∉ k := (List.nodup_cons.mp hnd).1
    rw [List.zip_cons_cons, List.map_cons, List.map_cons]
    congr 1
    · rw [applyValuation_eq, lookupSubst_cons_self]
    · rw [← map_applyValuation_zip (List.nodup_cons.mp hnd).2 (by simpa using hlen)]
      apply List.map_congr_left
      intro y hy
      have hne : x ≠ y := fun h => hx (h ▸ hy)
      rw [applyValuation_eq, applyValuation_eq, lookupSubst_cons_ne _ _ hne]

theorem applyValuation_zip_not_mem {ρ : Valuation} {k : List Nat} {v : List SubstVal}
    {x : Nat} (hx : x ∉ k) : applyValuation (k.zip v) ρ x = ρ x :=
  applyValuation_noSubst _ _ _ (lookupSubst_zip_none hx)

/-- A constant substitution entry. -/
def constSV (b : Bool) : SubstVal := if b then .one else .zero

theorem svEval_constSV (ρ : Valuation) (b : Bool) : svEval ρ (constSV b) = b := by
  cases b <;> rfl

/-- The valuation with `k[i] ↦ v[i]` and `false` elsewhere. -/
def assign (k : List Nat) (v : List Bool) : Valuation :=
  applyValuation (k.zip (v.map constSV)) (fun _ => false)

theorem map_assign {k : List Nat} {v : List Bool} (hnd : k.Nodup)
    (hlen : k.length = v.length) : k.map (assign k v) = v := by
  unfold assign
  rw [map_applyValuation_zip hnd (by simpa using hlen), List.map_map]
  conv => rhs; rw [← List.map_id v]
  exact List.map_congr_left (fun b _ => svEval_constSV _ b)

theorem map_split {f : Nat → Bool} {K₁ K₂ : List Nat} {V₁ V₂ : List Bool}
    (h : (K₁ ++ K₂).map f = V₁ ++ V₂) (hl : V₁.length = K₁.length) :
    K₁.map f = V₁ ∧ K₂.map f = V₂ := by
  rw [List.map_append] at h
  exact List.append_inj h (by simp [hl])

theorem map_svEval_posLit (ρ : Valuation) (K : List Nat) :
    (K.map SubstVal.posLit).map (svEval ρ) = K.map ρ := by
  rw [List.map_map]
  rfl

theorem sat_subst_list {σ : List (Nat × SubstVal)} {cs : List Constr} {ρ : Valuation} :
    (∀ c ∈ cs, (applySubstConstr σ c).sat ρ) ↔ ∀ c ∈ cs, c.sat (applyValuation σ ρ) :=
  ⟨fun h c hc => applySubstConstr_sat_rev σ c ρ (h c hc),
   fun h c hc => applySubstConstr_sound σ c ρ (h c hc)⟩

/-- Transfer satisfaction of constraints over `V` along a map equality on `V`. -/
theorem sat_transfer {cs : List Constr} {V : List Nat} {ρ ρ' : Valuation}
    (hv : ∀ c ∈ cs, ∀ x ∈ varsOf c, x ∈ V) (hag : V.map ρ = V.map ρ')
    (hs : ∀ c ∈ cs, c.sat ρ) : ∀ c ∈ cs, c.sat ρ' :=
  sat_list_of_agree hv (List.map_inj_left.mp hag) hs

theorem nodup_disj {l₁ l₂ : List Nat} (h : (l₁ ++ l₂).Nodup) {x : Nat} (hx : x ∈ l₁) :
    x ∉ l₂ :=
  fun hy => (List.nodup_append.mp h).2.2 x hx x hy rfl

/-! ## T7: order lemmas -/

/-- Reflexivity substitution `v ↦ u`. -/
def sigmaRefl (O : OrderData) : List (Nat × SubstVal) :=
  O.right.zip (O.left.map SubstVal.posLit)

/-- Transitivity substitution for `Spec(v,w,b)`, `Def(v,w,b)`: `u ↦ v, v ↦ w, a ↦ b`. -/
def sigmaVWB (O : OrderData) (w b : List Nat) : List (Nat × SubstVal) :=
  (O.left ++ O.right ++ O.aux).zip
    (O.right.map SubstVal.posLit ++ w.map SubstVal.posLit ++ b.map SubstVal.posLit)

/-- Transitivity substitution for `Spec(u,w,c)`, `Def(u,w,c)`: `v ↦ w, a ↦ c`. -/
def sigmaUWC (O : OrderData) (w c : List Nat) : List (Nat × SubstVal) :=
  (O.right ++ O.aux).zip (w.map SubstVal.posLit ++ c.map SubstVal.posLit)

/-- `σ≤ = [uᵢ ↦ ω̂(zᵢ), vᵢ ↦ zᵢ]` (aux untouched). -/
def sigmaLeq (O : OrderData) (z : List Literal) (ω : List (Nat × SubstVal)) :
    List (Nat × SubstVal) :=
  (O.left ++ O.right).zip (z.map (litSubst ω) ++ z.map litSV)

/-- `σ≥ = [uᵢ ↦ zᵢ, vᵢ ↦ ω̂(zᵢ)]` (aux untouched). -/
def sigmaGeq (O : OrderData) (z : List Literal) (ω : List (Nat × SubstVal)) :
    List (Nat × SubstVal) :=
  (O.left ++ O.right).zip (z.map litSV ++ z.map (litSubst ω))

/-- `refl_of_goals`: spec validity and the reflexivity goals give reflexivity. -/
theorem refl_of_goals {O : OrderData}
    (hwf : O.left.length = O.right.length ∧ (O.left ++ O.right ++ O.aux).Nodup)
    (hvars : ∀ c ∈ O.spec ++ O.defs, ∀ x ∈ varsOf c, x ∈ O.left ++ O.right ++ O.aux)
    (hspec : IsSpec O)
    (hgoal : ∀ ρ, (∀ g ∈ O.spec, (applySubstConstr (sigmaRefl O) g).sat ρ) →
      ∀ d ∈ O.defs, (applySubstConstr (sigmaRefl O) d).sat ρ) :
    ∀ p, p.length = O.left.length → O.Rel p p := by
  intro p hp
  have hLR : (O.left ++ O.right).Nodup := (List.nodup_append.mp hwf.2).1
  have hR : O.right.Nodup := (List.nodup_append.mp hLR).2.1
  have hAd : ∀ x ∈ O.left ++ O.right, x ∉ O.aux := fun x hx => nodup_disj hwf.2 hx
  have hLd : ∀ x ∈ O.left, x ∉ O.right := fun x hx => nodup_disj hLR hx
  have hτ : (O.left ++ O.right).map (assign (O.left ++ O.right) (p ++ p)) = p ++ p :=
    map_assign hLR (by simp [hp, hwf.1])
  obtain ⟨η, hηag, hηspec⟩ := hspec (assign (O.left ++ O.right) (p ++ p))
  have hηLR : (O.left ++ O.right).map η = p ++ p := by
    rw [← hτ]; exact List.map_congr_left (fun x hx => hηag x (hAd x hx))
  obtain ⟨hηL, hηR⟩ := map_split hηLR (by simp [hp])
  have hag : (O.left ++ O.right ++ O.aux).map (applyValuation (sigmaRefl O) η) =
      (O.left ++ O.right ++ O.aux).map η := by
    simp only [List.map_append]
    have h1 : O.left.map (applyValuation (sigmaRefl O) η) = O.left.map η :=
      List.map_congr_left (fun x hx => applyValuation_zip_not_mem (hLd x hx))
    have h2 : O.right.map (applyValuation (sigmaRefl O) η) = O.right.map η := by
      unfold sigmaRefl
      rw [map_applyValuation_zip hR (by simp [hwf.1]), map_svEval_posLit, hηL, hηR]
    have h3 : O.aux.map (applyValuation (sigmaRefl O) η) = O.aux.map η :=
      List.map_congr_left (fun x hx => applyValuation_zip_not_mem
        (fun hr => hAd x (List.mem_append_right _ hr) hx))
    rw [h1, h2, h3]
  have hvS : ∀ c ∈ O.spec, ∀ x ∈ varsOf c, x ∈ O.left ++ O.right ++ O.aux :=
    fun c hc => hvars c (List.mem_append_left _ hc)
  have hvD : ∀ c ∈ O.defs, ∀ x ∈ varsOf c, x ∈ O.left ++ O.right ++ O.aux :=
    fun c hc => hvars c (List.mem_append_right _ hc)
  have hspecσ := sat_subst_list.mpr (sat_transfer hvS hag.symm hηspec)
  have hdef := sat_transfer hvD hag (sat_subst_list.mp (hgoal η hspecσ))
  refine ⟨η, hηL, hηR, fun c hc => ?_⟩
  rcases List.mem_append.mp hc with hc | hc
  · exact hηspec c hc
  · exact hdef c hc

/-- `trans_of_goals`: spec validity, fresh lists `w`, `b`, `c` and the transitivity goals
give transitivity. -/
theorem trans_of_goals {O : OrderData} {w b c : List Nat}
    (hwf : O.left.length = O.right.length ∧ (O.left ++ O.right ++ O.aux).Nodup)
    (hvars : ∀ c ∈ O.spec ++ O.defs, ∀ x ∈ varsOf c, x ∈ O.left ++ O.right ++ O.aux)
    (hspec : IsSpec O)
    (hw : w.length = O.left.length) (hb : b.length = O.aux.length)
    (hc : c.length = O.aux.length)
    (hfresh : (O.left ++ O.right ++ O.aux ++ w ++ b ++ c).Nodup)
    (hgoal : ∀ ρ, (∀ g ∈ O.spec, g.sat ρ) →
      (∀ g ∈ O.spec, (applySubstConstr (sigmaVWB O w b) g).sat ρ) →
      (∀ g ∈ O.spec, (applySubstConstr (sigmaUWC O w c) g).sat ρ) →
      (∀ d ∈ O.defs, d.sat ρ) →
      (∀ d ∈ O.defs, (applySubstConstr (sigmaVWB O w b) d).sat ρ) →
      ∀ d ∈ O.defs, (applySubstConstr (sigmaUWC O w c) d).sat ρ) :
    ∀ p q r, O.Rel p q → O.Rel q r → O.Rel p r := by
  intro p q r ⟨η₁, h1L, h1R, h1s⟩ ⟨η₂, h2L, h2R, h2s⟩
  have hp : p.length = O.left.length := by rw [← h1L, List.length_map]
  have hq : q.length = O.right.length := by rw [← h1R, List.length_map]
  have hr : r.length = O.right.length := by rw [← h2R, List.length_map]
  have hLRA := hwf.2
  have hLR : (O.left ++ O.right).Nodup := (List.nodup_append.mp hLRA).1
  have hAd : ∀ x ∈ O.left ++ O.right, x ∉ O.aux := fun x hx => nodup_disj hLRA hx
  have hLRA' : (O.left ++ (O.right ++ O.aux)).Nodup := by rw [← List.append_assoc]; exact hLRA
  have hRA : (O.right ++ O.aux).Nodup := (List.nodup_append.mp hLRA').2.1
  have hLd : ∀ x ∈ O.left, x ∉ O.right ++ O.aux := fun x hx => nodup_disj hLRA' hx
  have hvS : ∀ c ∈ O.spec, ∀ x ∈ varsOf c, x ∈ O.left ++ O.right ++ O.aux :=
    fun c hc => hvars c (List.mem_append_left _ hc)
  have hvD : ∀ c ∈ O.defs, ∀ x ∈ varsOf c, x ∈ O.left ++ O.right ++ O.aux :=
    fun c hc => hvars c (List.mem_append_right _ hc)
  -- third witness from spec validity at keys (p, r)
  have hτ : (O.left ++ O.right).map (assign (O.left ++ O.right) (p ++ r)) = p ++ r :=
    map_assign hLR (by simp [hp, hr])
  obtain ⟨η₃, h3ag, h3spec⟩ := hspec (assign (O.left ++ O.right) (p ++ r))
  have h3LR : (O.left ++ O.right).map η₃ = p ++ r := by
    rw [← hτ]; exact List.map_congr_left (fun x hx => h3ag x (hAd x hx))
  obtain ⟨h3L, h3R⟩ := map_split h3LR (by simp [hp])
  -- the combined valuation
  let ρ := assign (O.left ++ O.right ++ O.aux ++ w ++ b ++ c)
    (p ++ q ++ O.aux.map η₁ ++ r ++ O.aux.map η₂ ++ O.aux.map η₃)
  have hρ : (O.left ++ O.right ++ O.aux ++ w ++ b ++ c).map ρ =
      p ++ q ++ O.aux.map η₁ ++ r ++ O.aux.map η₂ ++ O.aux.map η₃ :=
    map_assign hfresh (by simp [hp, hq, hr, hw, hb, hc, hwf.1])
  obtain ⟨hρ5, hρc⟩ := map_split hρ (by simp [hp, hq, hr, hw, hb, hwf.1])
  obtain ⟨hρ4, hρb⟩ := map_split hρ5 (by simp [hp, hq, hr, hw, hwf.1])
  obtain ⟨hρ3, hρw⟩ := map_split hρ4 (by simp [hp, hq])
  obtain ⟨hρ2, hρA⟩ := map_split hρ3 (by simp [hp, hq])
  obtain ⟨hρL, hρR⟩ := map_split hρ2 (by simp [hp])
  -- agreements
  have ag1 : (O.left ++ O.right ++ O.aux).map ρ = (O.left ++ O.right ++ O.aux).map η₁ := by
    simp only [List.map_append, hρL, hρR, hρA, h1L, h1R]
  have ag2 : (O.left ++ O.right ++ O.aux).map (applyValuation (sigmaVWB O w b) ρ) =
      (O.left ++ O.right ++ O.aux).map η₂ := by
    unfold sigmaVWB
    rw [map_applyValuation_zip hLRA (by simp [hw, hb, hwf.1])]
    simp only [List.map_append, map_svEval_posLit, hρR, hρw, hρb, h2L, h2R]
  have hσ2RA : (O.right ++ O.aux).map (applyValuation (sigmaUWC O w c) ρ) =
      w.map ρ ++ c.map ρ := by
    unfold sigmaUWC
    rw [map_applyValuation_zip hRA (by simp [hw, hc, hwf.1])]
    simp only [List.map_append, map_svEval_posLit]
  have hσ2L : O.left.map (applyValuation (sigmaUWC O w c) ρ) = O.left.map ρ :=
    List.map_congr_left (fun x hx => applyValuation_zip_not_mem (hLd x hx))
  obtain ⟨hσ2R, hσ2A⟩ := map_split hσ2RA (by simp [hw, hwf.1])
  have ag3 : (O.left ++ O.right ++ O.aux).map (applyValuation (sigmaUWC O w c) ρ) =
      (O.left ++ O.right ++ O.aux).map η₃ := by
    simp only [List.map_append] at hσ2A ⊢
    rw [hσ2L, hσ2R, hσ2A, hρL, hρw, hρc, h3L, h3R]
  -- the five premise blocks
  have hS1 : ∀ g ∈ O.spec, g.sat ρ :=
    sat_transfer hvS ag1.symm (fun g hg => h1s g (List.mem_append_left _ hg))
  have hS2 : ∀ g ∈ O.spec, (applySubstConstr (sigmaVWB O w b) g).sat ρ :=
    sat_subst_list.mpr (sat_transfer hvS ag2.symm (fun g hg => h2s g (List.mem_append_left _ hg)))
  have hS3 : ∀ g ∈ O.spec, (applySubstConstr (sigmaUWC O w c) g).sat ρ :=
    sat_subst_list.mpr (sat_transfer hvS ag3.symm h3spec)
  have hD1 : ∀ d ∈ O.defs, d.sat ρ :=
    sat_transfer hvD ag1.symm (fun g hg => h1s g (List.mem_append_right _ hg))
  have hD2 : ∀ d ∈ O.defs, (applySubstConstr (sigmaVWB O w b) d).sat ρ :=
    sat_subst_list.mpr (sat_transfer hvD ag2.symm (fun g hg => h2s g (List.mem_append_right _ hg)))
  have hD3 := sat_subst_list.mp (hgoal ρ hS1 hS2 hS3 hD1 hD2)
  refine ⟨applyValuation (sigmaUWC O w c) ρ, by rw [hσ2L, hρL], by rw [hσ2R, hρw], ?_⟩
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact sat_subst_list.mp hS3 d hd
  · exact hD3 d hd

theorem svVars_free_of_litSV {A : List Nat} {z : List Literal} (hz : ∀ l ∈ z, l.var ∉ A) :
    ∀ sv ∈ z.map litSV, ∀ j ∈ svVars sv, j ∉ A := by
  intro sv hsv j hj
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hsv
  rw [svVars_litSV, List.mem_singleton] at hj
  exact hj ▸ hz l hl

theorem litSubst_map_vars_free {A : List Nat} {z : List Literal} {ω : List (Nat × SubstVal)}
    (hz : ∀ l ∈ z, l.var ∉ A) (himg : ∀ l ∈ z, ImgFree ω A l.var) :
    ∀ sv ∈ z.map (litSubst ω), ∀ j ∈ svVars sv, j ∉ A := by
  intro sv hsv j hj
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hsv
  exact litSubst_vars_free (hz l hl) (himg l hl) j hj

theorem vars_free_append {A : List Nat} {X Y : List SubstVal}
    (hX : ∀ sv ∈ X, ∀ j ∈ svVars sv, j ∉ A) (hY : ∀ sv ∈ Y, ∀ j ∈ svVars sv, j ∉ A) :
    ∀ sv ∈ X ++ Y, ∀ j ∈ svVars sv, j ∉ A := by
  intro sv hsv
  rcases List.mem_append.mp hsv with h | h
  · exact hX sv h
  · exact hY sv h

/-- Pasting the aux values of `η` into `ρ`: the substituted paste agrees with `η` on
`L ∪ R ∪ A` when `η` has the substituted values of `ρ` on `L ∪ R`. -/
theorem paste_subst_agree {L R A : List Nat} {X Y : List SubstVal}
    (hnd : (L ++ R ++ A).Nodup) (hX : X.length = L.length) (hY : Y.length = R.length)
    (hfree : ∀ sv ∈ X ++ Y, ∀ j ∈ svVars sv, j ∉ A) {η ρ : Valuation}
    (hη : (L ++ R).map η = (X ++ Y).map (svEval ρ)) :
    (L ++ R ++ A).map (applyValuation ((L ++ R).zip (X ++ Y)) (paste A η ρ)) =
      (L ++ R ++ A).map η := by
  have hLR : (L ++ R).Nodup := (List.nodup_append.mp hnd).1
  have hlen : (L ++ R).length = (X ++ Y).length := by simp [hX, hY]
  rw [List.map_append, List.map_append (l₁ := L ++ R)]
  congr 1
  · rw [map_applyValuation_zip hLR hlen, hη]
    exact map_svEval_congr (fun sv hsv j hj => paste_of_not_mem (hfree sv hsv j hj))
  · apply List.map_congr_left
    intro x hx
    rw [applyValuation_zip_not_mem (fun h => nodup_disj hnd h hx), paste_of_mem hx]

/-- Extension by spec validity: for every `ρ` there is `ρ̂`, equal to `ρ` outside aux, whose
substituted valuation satisfies `spec` and carries the substituted values of `ρ`. -/
theorem exists_paste_ext {O : OrderData} {X Y : List SubstVal}
    (hnd : (O.left ++ O.right ++ O.aux).Nodup)
    (hvars : ∀ c ∈ O.spec ++ O.defs, ∀ x ∈ varsOf c, x ∈ O.left ++ O.right ++ O.aux)
    (hspec : IsSpec O) (hX : X.length = O.left.length) (hY : Y.length = O.right.length)
    (hfree : ∀ sv ∈ X ++ Y, ∀ j ∈ svVars sv, j ∉ O.aux) (ρ : Valuation) :
    ∃ ρ' : Valuation, (∀ x, x ∉ O.aux → ρ' x = ρ x) ∧
      (∀ s ∈ O.spec, s.sat (applyValuation ((O.left ++ O.right).zip (X ++ Y)) ρ')) ∧
      (O.left ++ O.right).map (applyValuation ((O.left ++ O.right).zip (X ++ Y)) ρ') =
        (X ++ Y).map (svEval ρ) := by
  have hLR : (O.left ++ O.right).Nodup := (List.nodup_append.mp hnd).1
  have hlen : (O.left ++ O.right).length = (X ++ Y).length := by simp [hX, hY]
  obtain ⟨η, hηag, hηspec⟩ := hspec (applyValuation ((O.left ++ O.right).zip (X ++ Y)) ρ)
  have hη : (O.left ++ O.right).map η = (X ++ Y).map (svEval ρ) := by
    rw [← map_applyValuation_zip (ρ := ρ) hLR hlen]
    exact List.map_congr_left (fun x hx => hηag x (nodup_disj hnd hx))
  have hag := paste_subst_agree hnd hX hY hfree hη
  refine ⟨paste O.aux η ρ, fun x hx => paste_of_not_mem hx,
    sat_transfer (fun c hc => hvars c (List.mem_append_left _ hc)) hag.symm hηspec, ?_⟩
  rw [← hη]
  have := (map_split (V₁ := (O.left ++ O.right).map η) (by rw [hag, List.map_append])
    (by simp))
  exact this.1

/-- `ordLeq_of_goal`: the order goals `Def[σ≤]`, proved under `G ∪ Spec[σ≤]`, give
`ρ∘ω ⪯ ρ` for every model `ρ` of `G`. -/
theorem ordLeq_of_goal {O : OrderData} {z : List Literal} {ω : List (Nat × SubstVal)}
    {G : List Constr}
    (hwf : O.left.length = O.right.length ∧ (O.left ++ O.right ++ O.aux).Nodup)
    (hvars : ∀ c ∈ O.spec ++ O.defs, ∀ x ∈ varsOf c, x ∈ O.left ++ O.right ++ O.aux)
    (hspec : IsSpec O) (hz : z.length = O.left.length)
    (hzaux : ∀ l ∈ z, l.var ∉ O.aux) (himg : ∀ l ∈ z, ImgFree ω O.aux l.var)
    (hGaux : ∀ g ∈ G, ∀ x ∈ varsOf g, x ∉ O.aux)
    (hgoal : ∀ ρ, (∀ g ∈ G, g.sat ρ) →
      (∀ s ∈ O.spec, (applySubstConstr (sigmaLeq O z ω) s).sat ρ) →
      ∀ d ∈ O.defs, (applySubstConstr (sigmaLeq O z ω) d).sat ρ) :
    ∀ ρ, (∀ g ∈ G, g.sat ρ) → Leq O z (applyValuation ω ρ) ρ := by
  intro ρ hρ
  obtain ⟨ρ', hag, hsp, hmap⟩ := exists_paste_ext (X := z.map (litSubst ω))
    (Y := z.map litSV) hwf.2 hvars hspec (by simp [hz]) (by simp [hz, hwf.1])
    (vars_free_append (litSubst_map_vars_free hzaux himg) (svVars_free_of_litSV hzaux)) ρ
  have hρ'G : ∀ g ∈ G, g.sat ρ' := fun g hg =>
    (sat_of_agree (fun x hx => (hag x (hGaux g hg x hx)).symm)).mp (hρ g hg)
  have hdef := sat_subst_list.mp (hgoal ρ' hρ'G (sat_subst_list.mpr hsp))
  rw [List.map_append (f := svEval ρ), ← key_comp_eq_map_litSubst, ← key_eq_map_litSV] at hmap
  obtain ⟨hL, hR⟩ := map_split hmap (by simp [hz])
  refine ⟨_, hL, hR, fun d hd => ?_⟩
  rcases List.mem_append.mp hd with hd | hd
  · exact hsp d hd
  · exact hdef d hd

/-- `ordStrict_of_goal`: unsatisfiability of `G ∪ Spec[σ≥] ∪ Def[σ≥]` gives
`¬ ρ ⪯ ρ∘ω` for every model `ρ` of `G`. No spec validity needed. -/
theorem ordStrict_of_goal {O : OrderData} {z : List Literal} {ω : List (Nat × SubstVal)}
    {G : List Constr}
    (hwf : O.left.length = O.right.length ∧ (O.left ++ O.right ++ O.aux).Nodup)
    (hvars : ∀ c ∈ O.spec ++ O.defs, ∀ x ∈ varsOf c, x ∈ O.left ++ O.right ++ O.aux)
    (hz : z.length = O.left.length)
    (hzaux : ∀ l ∈ z, l.var ∉ O.aux) (himg : ∀ l ∈ z, ImgFree ω O.aux l.var)
    (hGaux : ∀ g ∈ G, ∀ x ∈ varsOf g, x ∉ O.aux)
    (hgoal : ∀ ρ, (∀ g ∈ G, g.sat ρ) →
      (∀ s ∈ O.spec, (applySubstConstr (sigmaGeq O z ω) s).sat ρ) →
      (∀ d ∈ O.defs, (applySubstConstr (sigmaGeq O z ω) d).sat ρ) → False) :
    ∀ ρ, (∀ g ∈ G, g.sat ρ) → ¬ Leq O z ρ (applyValuation ω ρ) := by
  intro ρ hρ ⟨η, hL, hR, hsd⟩
  have hη : (O.left ++ O.right).map η = (z.map litSV ++ z.map (litSubst ω)).map (svEval ρ) := by
    rw [List.map_append, List.map_append, hL, hR, key_eq_map_litSV, key_comp_eq_map_litSubst]
  have hag := paste_subst_agree hwf.2 (by simp [hz]) (by simp [hz, hwf.1])
    (vars_free_append (svVars_free_of_litSV hzaux) (litSubst_map_vars_free hzaux himg)) hη
  have hsd' := sat_transfer hvars hag.symm hsd
  apply hgoal (paste O.aux η ρ)
  · exact fun g hg => (paste_sat (hGaux g hg)).mpr (hρ g hg)
  · exact sat_subst_list.mpr (fun s hs => hsd' s (List.mem_append_left _ hs))
  · exact sat_subst_list.mpr (fun d hd => hsd' d (List.mem_append_right _ hd))

/-- `specElim` (leq scope): an aux-free goal list `H` proved under `G ∪ Spec[σ≤]` holds for
every model of `G`. -/
theorem specElim_leq {O : OrderData} {z : List Literal} {ω : List (Nat × SubstVal)}
    {G H : List Constr}
    (hwf : O.left.length = O.right.length ∧ (O.left ++ O.right ++ O.aux).Nodup)
    (hvars : ∀ c ∈ O.spec ++ O.defs, ∀ x ∈ varsOf c, x ∈ O.left ++ O.right ++ O.aux)
    (hspec : IsSpec O) (hz : z.length = O.left.length)
    (hzaux : ∀ l ∈ z, l.var ∉ O.aux) (himg : ∀ l ∈ z, ImgFree ω O.aux l.var)
    (hGaux : ∀ g ∈ G, ∀ x ∈ varsOf g, x ∉ O.aux)
    (hHaux : ∀ h ∈ H, ∀ x ∈ varsOf h, x ∉ O.aux)
    (hgoal : ∀ ρ, (∀ g ∈ G, g.sat ρ) →
      (∀ s ∈ O.spec, (applySubstConstr (sigmaLeq O z ω) s).sat ρ) → ∀ h ∈ H, h.sat ρ) :
    ∀ ρ, (∀ g ∈ G, g.sat ρ) → ∀ h ∈ H, h.sat ρ := by
  intro ρ hρ
  obtain ⟨ρ', hag, hsp, _⟩ := exists_paste_ext (X := z.map (litSubst ω))
    (Y := z.map litSV) hwf.2 hvars hspec (by simp [hz]) (by simp [hz, hwf.1])
    (vars_free_append (litSubst_map_vars_free hzaux himg) (svVars_free_of_litSV hzaux)) ρ
  have hρ'G : ∀ g ∈ G, g.sat ρ' := fun g hg =>
    (sat_of_agree (fun x hx => (hag x (hGaux g hg x hx)).symm)).mp (hρ g hg)
  have hH := hgoal ρ' hρ'G (sat_subst_list.mpr hsp)
  exact fun h hh => (sat_of_agree (fun x hx => hag x (hHaux h hh x hx))).mp (hH h hh)

/-- `specElim` (geq scope): an aux-free goal list `H` proved under `G ∪ Spec[σ≥]` holds for
every model of `G`. -/
theorem specElim_geq {O : OrderData} {z : List Literal} {ω : List (Nat × SubstVal)}
    {G H : List Constr}
    (hwf : O.left.length = O.right.length ∧ (O.left ++ O.right ++ O.aux).Nodup)
    (hvars : ∀ c ∈ O.spec ++ O.defs, ∀ x ∈ varsOf c, x ∈ O.left ++ O.right ++ O.aux)
    (hspec : IsSpec O) (hz : z.length = O.left.length)
    (hzaux : ∀ l ∈ z, l.var ∉ O.aux) (himg : ∀ l ∈ z, ImgFree ω O.aux l.var)
    (hGaux : ∀ g ∈ G, ∀ x ∈ varsOf g, x ∉ O.aux)
    (hHaux : ∀ h ∈ H, ∀ x ∈ varsOf h, x ∉ O.aux)
    (hgoal : ∀ ρ, (∀ g ∈ G, g.sat ρ) →
      (∀ s ∈ O.spec, (applySubstConstr (sigmaGeq O z ω) s).sat ρ) → ∀ h ∈ H, h.sat ρ) :
    ∀ ρ, (∀ g ∈ G, g.sat ρ) → ∀ h ∈ H, h.sat ρ := by
  intro ρ hρ
  obtain ⟨ρ', hag, hsp, _⟩ := exists_paste_ext (X := z.map litSV)
    (Y := z.map (litSubst ω)) hwf.2 hvars hspec (by simp [hz]) (by simp [hz, hwf.1])
    (vars_free_append (svVars_free_of_litSV hzaux) (litSubst_map_vars_free hzaux himg)) ρ
  have hρ'G : ∀ g ∈ G, g.sat ρ' := fun g hg =>
    (sat_of_agree (fun x hx => (hag x (hGaux g hg x hx)).symm)).mp (hρ g hg)
  have hH := hgoal ρ' hρ'G (sat_subst_list.mpr hsp)
  exact fun h hh => (sat_of_agree (fun x hx => hag x (hHaux h hh x hx))).mp (hH h hh)

/-- Freshness bridge for `specElim`: if a constraint has no aux variable (F1) and `ω` maps
none of its variables onto an aux variable (F4), then `c|ω` has no aux variable. -/
theorem substRemainingTerms_free {ω : List (Nat × SubstVal)} {A : List Nat} :
    ∀ {ts : List Term}, (∀ t ∈ ts, t.2.var ∉ A) → (∀ t ∈ ts, ImgFree ω A t.2.var) →
    ∀ t ∈ substRemainingTerms ω ts, t.2.var ∉ A
  | [], _, _ => by simp [substRemainingTerms]
  | (a, l) :: rest, h1, h2 => by
    have ih := substRemainingTerms_free (ts := rest)
      (fun t ht => h1 t (List.mem_cons_of_mem _ ht))
      (fun t ht => h2 t (List.mem_cons_of_mem _ ht))
    have hhead : ∀ t', (applySubstTerm ω a l).2 = some t' → t'.2.var ∉ A := by
      intro t' hst
      unfold applySubstTerm at hst
      cases hlk : lookupSubst ω l.var with
      | none =>
        rw [hlk] at hst
        simp only [Option.some.injEq] at hst
        subst hst
        exact h1 (a, l) List.mem_cons_self
      | some sv =>
        rw [hlk] at hst
        have hfree := h2 (a, l) List.mem_cons_self sv hlk
        cases sv <;> cases l <;> simp only [Option.some.injEq, reduceCtorEq] at hst <;>
          subst hst <;> simp only [svVars, List.mem_singleton, forall_eq] at hfree <;>
          exact hfree
    intro t ht
    simp only [substRemainingTerms] at ht
    revert ht
    cases hst : (applySubstTerm ω a l).2 with
    | none => exact ih t
    | some t' =>
      intro ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hhead _ hst
      · exact ih t ht

theorem varsOf_applySubstConstr_free {ω : List (Nat × SubstVal)} {A : List Nat} {c : Constr}
    (h1 : ∀ x ∈ varsOf c, x ∉ A) (h2 : ∀ x ∈ varsOf c, ImgFree ω A x) :
    ∀ x ∈ varsOf (applySubstConstr ω c), x ∉ A := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact substRemainingTerms_free (fun t ht => h1 _ (List.mem_map_of_mem ht))
    (fun t ht => h2 _ (List.mem_map_of_mem ht)) t ht

-- A witness that maps no variable of `z` keeps the key. -/
theorem key_applyValuation_of_untouched {z : List Literal} {ω : List (Nat × SubstVal)}
    (h : ∀ l ∈ z, lookupSubst ω l.var = none) (ρ : Valuation) :
    key z (applyValuation ω ρ) = key z ρ := by
  unfold key
  apply List.map_congr_left
  intro l hl
  cases l with
  | pos i => exact applyValuation_noSubst ω ρ i (h _ hl)
  | neg i => simp only [litBool]; rw [applyValuation_noSubst ω ρ i (h _ hl)]

/-- With an untouched witness the order goal holds by reflexivity. -/
theorem leq_of_untouched {O : OrderData} {z : List Literal} {ω : List (Nat × SubstVal)}
    (hrefl : ∀ p, p.length = O.left.length → O.Rel p p) (hz : z.length = O.left.length)
    (h : ∀ l ∈ z, lookupSubst ω l.var = none) (ρ : Valuation) :
    Leq O z (applyValuation ω ρ) ρ := by
  unfold Leq
  rw [key_applyValuation_of_untouched h ρ]
  exact leq_refl hrefl hz ρ

/-- A chain of redundance steps with witnesses supported in `A`: each `gᵢ` is derivable
from the earlier ones (`pre`). -/
def RedChain (A : List Nat) : List Constr → List (Constr × List (Nat × SubstVal)) → Prop
  | _, [] => True
  | pre, (g, ω) :: rest =>
    (∀ p ∈ ω, p.1 ∈ A) ∧
    (∀ ρ, (∀ c ∈ pre, c.sat ρ) → ¬ g.sat ρ → ∀ c ∈ pre ++ [g], c.sat (applyValuation ω ρ)) ∧
    RedChain A (pre ++ [g]) rest

theorem redChain_ext {A : List Nat} : ∀ {pre : List Constr}
    {steps : List (Constr × List (Nat × SubstVal))}, RedChain A pre steps →
    (∀ ρ : Valuation, ∃ ρ' : Valuation, (∀ x, x ∉ A → ρ' x = ρ x) ∧ ∀ c ∈ pre, c.sat ρ') →
    ∀ ρ : Valuation, ∃ ρ' : Valuation, (∀ x, x ∉ A → ρ' x = ρ x) ∧
      ∀ c ∈ pre ++ steps.map Prod.fst, c.sat ρ'
  | pre, [], _, h => by simpa using h
  | pre, (g, ω) :: rest, ⟨hsupp, hred, hrest⟩, h => by
    have h' : ∀ ρ : Valuation, ∃ ρ' : Valuation, (∀ x, x ∉ A → ρ' x = ρ x) ∧
        ∀ c ∈ pre ++ [g], c.sat ρ' := by
      intro ρ
      obtain ⟨ρ', hag, hsat⟩ := h ρ
      rcases Classical.em (g.sat ρ') with hg | hg
      · refine ⟨ρ', hag, fun c hc => ?_⟩
        rcases List.mem_append.mp hc with hc | hc
        · exact hsat c hc
        · rw [List.mem_singleton] at hc; exact hc ▸ hg
      · refine ⟨applyValuation ω ρ', fun x hx => ?_, hred ρ' hsat hg⟩
        rw [applyValuation_noSubst _ _ _
          (lookupSubst_none_of_not_key (fun p hp hpx => hx (by rw [← hpx]; exact hsupp p hp)))]
        exact hag x hx
    have := redChain_ext hrest h'
    simpa [List.append_assoc] using this

/-- `spec_valid`: a spec derived by a chain of redundance steps with witnesses supported in
the aux variables is valid. -/
theorem spec_valid {O : OrderData} {steps : List (Constr × List (Nat × SubstVal))}
    (hsteps : O.spec = steps.map Prod.fst) (hchain : RedChain O.aux [] steps) : IsSpec O := by
  intro ρ
  obtain ⟨ρ', hag, hsat⟩ := redChain_ext hchain
    (fun ρ => ⟨ρ, fun _ _ => rfl, fun _ hc => absurd hc List.not_mem_nil⟩) ρ
  refine ⟨ρ', hag, ?_⟩
  rw [hsteps]
  simpa using hsat

end Sat.PB.Dominance
