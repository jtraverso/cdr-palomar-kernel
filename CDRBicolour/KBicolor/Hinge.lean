/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Host
public import CDRBicolour.Absorption.Hinge

/-!
# k-bicolourings: hypothesis H4 (hinges)

The octahedral hinge of `CDRBicolour.Absorption.Hinge` uses only that `x` lies in the class of
`u` and `y` in the class of `v`: the six triangles of its two decompositions have the label
multiset of `{u,v,a}` or of `{u,v,b}`. So it works verbatim for `k` classes. If every class has
at least `δ n ≥ 10` points, there are at least `(δ n / 2)²` hinges of order `6`, i.e.
`HingeCond` holds with `α = δ² / 4`, `h = 6`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle
open CDRBicolour.Absorption (hcore Six support_hcore hcore_inj ne_of_card_three val_map_triple
  triEdges_triple)

section Gadget

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem isAllowed_triple (lab : V → Fin k) {x y z : V} (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (hF : ({lab x, lab y, lab z} : Multiset (Fin k)) ∈ bicF k) :
    IsAllowed (kHost lab) (bicF k) {x, y, z} := by
  refine ⟨card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩, fun u _ v _ huv => ?_, ?_⟩
  · simpa [kHost] using huv
  · rw [val_map_triple lab hxy (Ne.symm hxz) (Ne.symm hyz)]; exact hF

theorem isDecomposition_three (lab : V → Fin k) {T1 T2 T3 : Finset V} {J : Finset (Sym2 V)}
    (h1 : IsAllowed (kHost lab) (bicF k) T1) (h2 : IsAllowed (kHost lab) (bicF k) T2)
    (h3 : IsAllowed (kHost lab) (bicF k) T3) (d12 : Disjoint (triEdges T1) (triEdges T2))
    (d13 : Disjoint (triEdges T1) (triEdges T3)) (d23 : Disjoint (triEdges T2) (triEdges T3))
    (hcov : triEdges T1 ∪ triEdges T2 ∪ triEdges T3 = J) :
    IsDecomposition (kHost lab) (bicF k) J {T1, T2, T3} := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    simp only [mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  · intro T hT T' hT' hne
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hT hT'
    rcases hT with rfl | rfl | rfl <;> rcases hT' with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | exact d12
      | exact d13
      | exact d23
      | exact d12.symm
      | exact d13.symm
      | exact d23.symm
  · rw [← hcov]
    ext e
    simp only [mem_biUnion, mem_insert, mem_singleton, mem_union]
    constructor
    · rintro ⟨T, hT, he⟩
      rcases hT with rfl | rfl | rfl <;> tauto
    · rintro ((he | he) | he)
      · exact ⟨T1, Or.inl rfl, he⟩
      · exact ⟨T2, Or.inr (Or.inl rfl), he⟩
      · exact ⟨T3, Or.inr (Or.inr rfl), he⟩

theorem mem_edges_kHost (lab : V → Fin k) {p q : V} (h : p ≠ q) :
    s(p, q) ∈ edges (kHost lab) := by
  simp [edges, h]

set_option maxHeartbeats 1000000 in
/-- The octahedral core is a hinge for `{u,v,a}`, `{u,v,b}` when `x ~ u` and `y ~ v`. -/
theorem hcore_isHinge (lab : V → Fin k) {u v a b x y : V} (h : Six u v a b x y)
    (hlx : lab x = lab u) (hly : lab y = lab v)
    (hFa : ({lab u, lab v, lab a} : Multiset (Fin k)) ∈ bicF k)
    (hFb : ({lab u, lab v, lab b} : Multiset (Fin k)) ∈ bicF k) :
    IsHinge (kHost lab) (bicF k) u v a b (hcore u v a b x y) := by
  obtain ⟨uv, ua, ub, ux, uy, va, vb, vx, vy, ab, ax, ay, bx, by', xy⟩ := h
  have vu := uv.symm; have au := ua.symm; have bu := ub.symm; have xu := ux.symm
  have yu := uy.symm; have av := va.symm; have bv := vb.symm; have xv := vx.symm
  have yv := vy.symm; have ba := ab.symm; have xa := ax.symm; have ya := ay.symm
  have xb := bx.symm; have yb := by'.symm; have yx := xy.symm
  have A1 : IsAllowed (kHost lab) (bicF k) {u, y, a} :=
    isAllowed_triple lab uy ua ya (by rw [hly]; exact hFa)
  have A2 : IsAllowed (kHost lab) (bicF k) {x, v, a} :=
    isAllowed_triple lab xv xa va (by rw [hlx]; exact hFa)
  have A3 : IsAllowed (kHost lab) (bicF k) {x, y, b} :=
    isAllowed_triple lab xy xb yb (by rw [hlx, hly]; exact hFb)
  have B1 : IsAllowed (kHost lab) (bicF k) {u, y, b} :=
    isAllowed_triple lab uy ub yb (by rw [hly]; exact hFb)
  have B2 : IsAllowed (kHost lab) (bicF k) {x, v, b} :=
    isAllowed_triple lab xv xb vb (by rw [hlx]; exact hFb)
  have B3 : IsAllowed (kHost lab) (bicF k) {x, y, a} :=
    isAllowed_triple lab xy xa ya (by rw [hlx, hly]; exact hFa)
  refine ⟨?_, ?_, ⟨{{u, y, a}, {x, v, a}, {x, y, b}}, ?_⟩,
    ⟨{{u, y, b}, {x, v, b}, {x, y, a}}, ?_⟩⟩
  · intro e he
    simp only [hcore, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact mem_edges_kHost lab ‹_›
  · rw [disjoint_left]
    intro e he he'
    simp only [hcore, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [triEdges, mem_union, mem_filter, mk_mem_sym2_iff, mem_insert, mem_singleton,
        Sym2.mk_isDiag_iff] at he' <;> simp_all
  · refine isDecomposition_three lab A1 A2 A3 ?_ ?_ ?_ ?_
    · rw [triEdges_triple uy ua ya, triEdges_triple xv xa va, disjoint_left]
      intro e he he'; simp only [mem_insert, mem_singleton] at he he'
      rcases he with rfl | rfl | rfl <;> simp_all [Sym2.eq_iff]
    · rw [triEdges_triple uy ua ya, triEdges_triple xy xb yb, disjoint_left]
      intro e he he'; simp only [mem_insert, mem_singleton] at he he'
      rcases he with rfl | rfl | rfl <;> simp_all [Sym2.eq_iff]
    · rw [triEdges_triple xv xa va, triEdges_triple xy xb yb, disjoint_left]
      intro e he he'; simp only [mem_insert, mem_singleton] at he he'
      rcases he with rfl | rfl | rfl <;> simp_all [Sym2.eq_iff]
    · rw [triEdges_triple uy ua ya, triEdges_triple xv xa va, triEdges_triple xy xb yb]
      ext e
      simp only [hcore, wedge, mem_union, mem_insert, mem_singleton]
      tauto
  · refine isDecomposition_three lab B1 B2 B3 ?_ ?_ ?_ ?_
    · rw [triEdges_triple uy ub yb, triEdges_triple xv xb vb, disjoint_left]
      intro e he he'; simp only [mem_insert, mem_singleton] at he he'
      rcases he with rfl | rfl | rfl <;> simp_all [Sym2.eq_iff]
    · rw [triEdges_triple uy ub yb, triEdges_triple xy xa ya, disjoint_left]
      intro e he he'; simp only [mem_insert, mem_singleton] at he he'
      rcases he with rfl | rfl | rfl <;> simp_all [Sym2.eq_iff]
    · rw [triEdges_triple xv xb vb, triEdges_triple xy xa ya, disjoint_left]
      intro e he he'; simp only [mem_insert, mem_singleton] at he he'
      rcases he with rfl | rfl | rfl <;> simp_all [Sym2.eq_iff]
    · rw [triEdges_triple uy ub yb, triEdges_triple xv xb vb, triEdges_triple xy xa ya]
      ext e
      simp only [hcore, wedge, mem_union, mem_insert, mem_singleton]
      tauto

/-- At least `|X| (|Y| - 1)` hinges of order `6`, with `X` (resp. `Y`) the class of `u`
(resp. `v`) minus `{u, v, a, b}`. -/
theorem hinges_card_ge (lab : V → Fin k) {u v a b : V} (hab : a ≠ b)
    (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hub : u ≠ b) (hvb : v ≠ b)
    (hFa : ({lab u, lab v, lab a} : Multiset (Fin k)) ∈ bicF k)
    (hFb : ({lab u, lab v, lab b} : Multiset (Fin k)) ∈ bicF k) :
    let X := (univ.filter fun w => lab w = lab u) \ {u, v, a, b}
    let Y := (univ.filter fun w => lab w = lab v) \ {u, v, a, b}
    X.card * Y.card - X.card ≤ (hinges (kHost lab) (bicF k) u v a b 6).card := by
  intro X Y
  set P := (X ×ˢ Y).filter fun p : V × V => p.1 ≠ p.2 with hP
  have hmemX : ∀ x ∈ X, lab x = lab u ∧ x ≠ u ∧ x ≠ v ∧ x ≠ a ∧ x ≠ b := by
    intro x hx
    simp only [X, mem_sdiff, mem_filter, mem_univ, true_and, mem_insert, mem_singleton] at hx
    tauto
  have hmemY : ∀ y ∈ Y, lab y = lab v ∧ y ≠ u ∧ y ≠ v ∧ y ≠ a ∧ y ≠ b := by
    intro y hy
    simp only [Y, mem_sdiff, mem_filter, mem_univ, true_and, mem_insert, mem_singleton] at hy
    tauto
  have hsix : ∀ p ∈ P, Six u v a b p.1 p.2 := by
    intro p hp
    simp only [hP, mem_filter, mem_product] at hp
    obtain ⟨⟨hx, hy⟩, hxy⟩ := hp
    obtain ⟨-, x1, x2, x3, x4⟩ := hmemX _ hx
    obtain ⟨-, y1, y2, y3, y4⟩ := hmemY _ hy
    exact ⟨huv, hua, hub, Ne.symm x1, Ne.symm y1, hva, hvb, Ne.symm x2, Ne.symm y2, hab,
      Ne.symm x3, Ne.symm y3, Ne.symm x4, Ne.symm y4, hxy⟩
  have hsub : P.image (fun p => hcore u v a b p.1 p.2) ⊆
      hinges (kHost lab) (bicF k) u v a b 6 := by
    intro J hJ
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hJ
    have hpm := mem_filter.1 hp
    have hx := hmemX _ (mem_product.1 hpm.1).1
    have hy := hmemY _ (mem_product.1 hpm.1).2
    simp only [hinges, mem_filter, mem_univ, true_and]
    exact ⟨hcore_isHinge lab (hsix p hp) hx.1 hy.1 hFa hFb, support_hcore (hsix p hp)⟩
  have hinj : Set.InjOn (fun p : V × V => hcore u v a b p.1 p.2) P := by
    intro p hp q hq he
    obtain ⟨h1, h2⟩ := hcore_inj (hsix p hp) (hsix q hq) he
    exact Prod.ext h1 h2
  have hcardP : X.card * Y.card - X.card ≤ P.card := by
    have hsplit : P.card + ((X ×ˢ Y).filter fun p : V × V => ¬ p.1 ≠ p.2).card =
        (X ×ˢ Y).card := by
      rw [hP]; exact card_filter_add_card_filter_not _
    have hdiag : ((X ×ˢ Y).filter fun p : V × V => ¬ p.1 ≠ p.2).card ≤ X.card := by
      apply card_le_card_of_injOn (fun p => p.1)
      · intro p hp
        exact (mem_product.1 (mem_filter.1 hp).1).1
      · intro p hp q hq he
        have hp2 := (mem_filter.1 hp).2
        have hq2 := (mem_filter.1 hq).2
        simp only [ne_eq, not_not] at hp2 hq2
        exact Prod.ext he (by rw [← hp2, ← hq2]; exact he)
    rw [card_product] at hsplit
    omega
  calc X.card * Y.card - X.card ≤ P.card := hcardP
    _ = (P.image fun p => hcore u v a b p.1 p.2).card := (card_image_of_injOn hinj).symm
    _ ≤ _ := card_le_card hsub

end Gadget

section HingeCond

variable {k : ℕ} {V : Type*} [Fintype V]

theorem card_class_sdiff [DecidableEq V] (lab : V → Fin k) (u v a b : V) (X : Fin k) :
    ksz lab X ≤ ((univ.filter fun w => lab w = X) \ {u, v, a, b}).card + 4 := by
  have h1 := le_card_sdiff ({u, v, a, b} : Finset V) (univ.filter fun w => lab w = X)
  have h2 := card_le_four (a := u) (b := v) (c := a) (d := b)
  unfold ksz
  omega

/-- **H4**: classes of size at least `δ n`, `δ n ≥ 10`, give `α = δ² / 4`, `h = 6`. -/
theorem kH4 (lab : V → Fin k) {δ : ℝ} (hδ : 0 < δ)
    (hcls : ∀ X, δ * Fintype.card V ≤ ksz lab X) (h10 : 10 ≤ δ * Fintype.card V) :
    HingeCond (kHost lab) (bicF k) (δ ^ 2 / 4) 6 := by
  classical
  intro u v a b hab hTa hTb
  refine ⟨6, le_rfl, le_rfl, ?_⟩
  obtain ⟨huv, hua, hva⟩ := ne_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := ne_of_card_three hTb.1
  have hFa : ({lab u, lab v, lab a} : Multiset (Fin k)) ∈ bicF k := by
    have := hTa.2.2; rwa [val_map_triple lab huv (Ne.symm hua) (Ne.symm hva)] at this
  have hFb : ({lab u, lab v, lab b} : Multiset (Fin k)) ∈ bicF k := by
    have := hTb.2.2; rwa [val_map_triple lab huv (Ne.symm hub) (Ne.symm hvb)] at this
  have hc := hinges_card_ge lab hab huv hua hva hub hvb hFa hFb
  simp only at hc
  have hX0 := card_class_sdiff lab u v a b (lab u)
  have hY0 := card_class_sdiff lab u v a b (lab v)
  generalize ((univ.filter fun w => lab w = lab u) \ {u, v, a, b}) = X at hc hX0
  generalize ((univ.filter fun w => lab w = lab v) \ {u, v, a, b}) = Y at hc hY0
  set n : ℝ := (Fintype.card V : ℝ)
  have hXR : δ * n ≤ (X.card : ℝ) + 4 := by
    have := hcls (lab u); have : (ksz lab (lab u) : ℝ) ≤ X.card + 4 := by exact_mod_cast hX0
    linarith
  have hYR : δ * n ≤ (Y.card : ℝ) + 4 := by
    have := hcls (lab v); have : (ksz lab (lab v) : ℝ) ≤ Y.card + 4 := by exact_mod_cast hY0
    linarith
  have hY1 : 1 ≤ Y.card := by
    have : (6 : ℝ) ≤ Y.card := by linarith
    exact_mod_cast (by linarith : (1 : ℝ) ≤ Y.card)
  have hle : X.card ≤ X.card * Y.card := Nat.le_mul_of_pos_right _ hY1
  have hcR : ((X.card : ℝ) * Y.card - X.card) ≤ (hinges (kHost lab) (bicF k) u v a b 6).card := by
    have : ((X.card * Y.card - X.card : ℕ) : ℝ) ≤ (hinges (kHost lab) (bicF k) u v a b 6).card := by
      exact_mod_cast hc
    rwa [Nat.cast_sub hle, Nat.cast_mul] at this
  norm_num only [Nat.reduceSub]
  refine le_trans ?_ hcR
  have k1 : δ * n / 2 ≤ X.card := by linarith
  have k2 : δ * n / 2 ≤ (Y.card : ℝ) - 1 := by linarith
  have k3 := mul_le_mul k1 k2 (by positivity) (by linarith)
  nlinarith

end HingeCond

end CDRBicolour.KBicolor
