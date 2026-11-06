/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Lattice

/-!
# The CDR host for Paper III: hypothesis H4 (hinges)

The octahedral hinge of Paper III (`ApplicationsOctahedron*`), written directly in the host.
For allowed triangles `{u,v,a}` and `{u,v,b}`, take `x` in the class of `u` and `y` in the class
of `v`, all six points distinct. The core

  `J = {uy, xv, xy, xa, xb, ya, yb}`

satisfies

* `J ∪ {ua, va}` = edges of `{u,y,a}`, `{x,v,a}`, `{x,y,b}`;
* `J ∪ {ub, vb}` = edges of `{u,y,b}`, `{x,v,b}`, `{x,y,a}`.

Every one of these six triangles has the label multiset of `{u,v,a}` or of `{u,v,b}`, hence is
allowed. Distinct `(x, y)` give distinct cores, so there are at least `n²/32` hinges of order `6`
once `n ≥ 400` (each class has at least `n/4 + 2` points).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

section Hinge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The octahedral hinge core. -/
def hcore (u v a b x y : V) : Finset (Sym2 V) :=
  {s(u, y), s(x, v), s(x, y), s(x, a), s(x, b), s(y, a), s(y, b)}

/-- Six pairwise distinct points. -/
structure Six (u v a b x y : V) : Prop where
  uv : u ≠ v
  ua : u ≠ a
  ub : u ≠ b
  ux : u ≠ x
  uy : u ≠ y
  va : v ≠ a
  vb : v ≠ b
  vx : v ≠ x
  vy : v ≠ y
  ab : a ≠ b
  ax : a ≠ x
  ay : a ≠ y
  bx : b ≠ x
  by' : b ≠ y
  xy : x ≠ y

theorem isDecomposition_three (lab : V → Fin 3) {T1 T2 T3 : Finset V} {J : Finset (Sym2 V)}
    (h1 : IsAllowed (cHost lab) cdrF T1) (h2 : IsAllowed (cHost lab) cdrF T2)
    (h3 : IsAllowed (cHost lab) cdrF T3) (d12 : Disjoint (triEdges T1) (triEdges T2))
    (d13 : Disjoint (triEdges T1) (triEdges T3)) (d23 : Disjoint (triEdges T2) (triEdges T3))
    (hcov : triEdges T1 ∪ triEdges T2 ∪ triEdges T3 = J) :
    IsDecomposition (cHost lab) cdrF J {T1, T2, T3} := by
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

theorem mem_edges_cHost (lab : V → Fin 3) {p q : V} (h : p ≠ q) :
    s(p, q) ∈ edges (cHost lab) := by
  simp [edges, h]

/-- The octahedral core is a hinge for `{u,v,a}`, `{u,v,b}` when `x ~ u` and `y ~ v`. -/
theorem hcore_isHinge (lab : V → Fin 3) {u v a b x y : V} (h : Six u v a b x y)
    (hlx : lab x = lab u) (hly : lab y = lab v)
    (hFa : ({lab u, lab v, lab a} : Multiset (Fin 3)) ∈ cdrF)
    (hFb : ({lab u, lab v, lab b} : Multiset (Fin 3)) ∈ cdrF) :
    IsHinge (cHost lab) cdrF u v a b (hcore u v a b x y) := by
  obtain ⟨uv, ua, ub, ux, uy, va, vb, vx, vy, ab, ax, ay, bx, by', xy⟩ := h
  have vu := uv.symm; have au := ua.symm; have bu := ub.symm; have xu := ux.symm
  have yu := uy.symm; have av := va.symm; have bv := vb.symm; have xv := vx.symm
  have yv := vy.symm; have ba := ab.symm; have xa := ax.symm; have ya := ay.symm
  have xb := bx.symm; have yb := by'.symm; have yx := xy.symm
  -- the six triangles are allowed
  have A1 : IsAllowed (cHost lab) cdrF {u, y, a} :=
    isAllowed_triple lab uy ua ya (by rw [hly]; exact hFa)
  have A2 : IsAllowed (cHost lab) cdrF {x, v, a} :=
    isAllowed_triple lab xv xa va (by rw [hlx]; exact hFa)
  have A3 : IsAllowed (cHost lab) cdrF {x, y, b} :=
    isAllowed_triple lab xy xb yb (by rw [hlx, hly]; exact hFb)
  have B1 : IsAllowed (cHost lab) cdrF {u, y, b} :=
    isAllowed_triple lab uy ub yb (by rw [hly]; exact hFb)
  have B2 : IsAllowed (cHost lab) cdrF {x, v, b} :=
    isAllowed_triple lab xv xb vb (by rw [hlx]; exact hFb)
  have B3 : IsAllowed (cHost lab) cdrF {x, y, a} :=
    isAllowed_triple lab xy xa ya (by rw [hlx, hly]; exact hFa)
  refine ⟨?_, ?_, ⟨{{u, y, a}, {x, v, a}, {x, y, b}}, ?_⟩,
    ⟨{{u, y, b}, {x, v, b}, {x, y, a}}, ?_⟩⟩
  · intro e he
    simp only [hcore, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact mem_edges_cHost lab ‹_›
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

theorem support_hcore {u v a b x y : V} (h : Six u v a b x y) :
    (support (hcore u v a b x y)).card = 6 := by
  obtain ⟨uv, ua, ub, ux, uy, va, vb, vx, vy, ab, ax, ay, bx, by', xy⟩ := h
  have hs : support (hcore u v a b x y) = {u, v, a, b, x, y} := by
    ext w
    simp only [support, hcore, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
      exists_eq_or_imp, exists_eq_left, Sym2.mem_iff]
    tauto
  rw [hs, card_insert_of_notMem (by simp [uv, ua, ub, ux, uy]),
    card_insert_of_notMem (by simp [va, vb, vx, vy]), card_insert_of_notMem (by simp [ab, ax, ay]),
    card_insert_of_notMem (by simp [bx, by']), card_pair xy]

theorem hcore_inj {u v a b x y x' y' : V} (h : Six u v a b x y) (h' : Six u v a b x' y')
    (he : hcore u v a b x y = hcore u v a b x' y') : x = x' ∧ y = y' := by
  have h1 : s(u, y) ∈ hcore u v a b x' y' := by rw [← he]; simp [hcore]
  have h2 : s(x, v) ∈ hcore u v a b x' y' := by rw [← he]; simp [hcore]
  obtain ⟨uv, ua, ub, ux, uy, va, vb, vx, vy, ab, ax, ay, bx, by', xy⟩ := h'
  obtain ⟨-, -, -, ux0, uy0, -, -, vx0, vy0, -, ax0, ay0, bx0, by0, xy0⟩ := h
  simp only [hcore, mem_insert, mem_singleton, Sym2.eq_iff] at h1 h2
  constructor
  · rcases h2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 <;> simp_all
  · rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all

/-- At least `|X| (|Y| - 1)` hinges of order `6`, with `X` (resp. `Y`) the class of `u`
(resp. `v`) minus `{u, v, a, b}`. -/
theorem hinges_card_ge (lab : V → Fin 3) {u v a b : V} (hab : a ≠ b)
    (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hub : u ≠ b) (hvb : v ≠ b)
    (hFa : ({lab u, lab v, lab a} : Multiset (Fin 3)) ∈ cdrF)
    (hFb : ({lab u, lab v, lab b} : Multiset (Fin 3)) ∈ cdrF) :
    let X := (univ.filter fun w => lab w = lab u) \ {u, v, a, b}
    let Y := (univ.filter fun w => lab w = lab v) \ {u, v, a, b}
    X.card * Y.card - X.card ≤ (hinges (cHost lab) cdrF u v a b 6).card := by
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
  have hsub : P.image (fun p => hcore u v a b p.1 p.2) ⊆ hinges (cHost lab) cdrF u v a b 6 := by
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

end Hinge

section HingeCond

variable {V : Type*} [Fintype V]

theorem card_class_sdiff [DecidableEq V] (lab : V → Fin 3) (u v a b : V) (k : Fin 3) :
    csz lab k ≤ ((univ.filter fun w => lab w = k) \ {u, v, a, b}).card + 4 := by
  have h1 := le_card_sdiff ({u, v, a, b} : Finset V) (univ.filter fun w => lab w = k)
  have h2 := card_le_four (a := u) (b := v) (c := a) (d := b)
  unfold csz
  omega

theorem ne_of_card_three [DecidableEq V] {u v a : V} (h : ({u, v, a} : Finset V).card = 3) :
    u ≠ v ∧ u ≠ a ∧ v ≠ a := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · have : ({u, v, a} : Finset V) ⊆ {u, a} := by
      intro w hw; simp only [mem_insert, mem_singleton] at hw ⊢; rw [← e] at hw; tauto
    have := card_le_card this; have := card_le_two (a := u) (b := a); omega
  · have : ({u, v, a} : Finset V) ⊆ {u, v} := by
      intro w hw; simp only [mem_insert, mem_singleton] at hw ⊢; rw [← e] at hw; tauto
    have := card_le_card this; have := card_le_two (a := u) (b := v); omega
  · have : ({u, v, a} : Finset V) ⊆ {u, v} := by
      intro w hw; simp only [mem_insert, mem_singleton] at hw ⊢; rw [← e] at hw; tauto
    have := card_le_card this; have := card_le_two (a := u) (b := v); omega

/-- **H4, general form**: if every class has at least `(N + 8)/4` points (`N = |V| ≥ 400`), the
hinge condition holds with `α = 1/32`, `h = 6`. -/
theorem hingeCond_of (lab : V → Fin 3) (hN : 400 ≤ Fintype.card V)
    (hcls : ∀ k, Fintype.card V + 8 ≤ 4 * csz lab k) :
    HingeCond (cHost lab) cdrF (1 / 32) 6 := by
  classical
  intro u v a b hab hTa hTb
  refine ⟨6, le_rfl, le_rfl, ?_⟩
  obtain ⟨huv, hua, hva⟩ := ne_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := ne_of_card_three hTb.1
  have hFa : ({lab u, lab v, lab a} : Multiset (Fin 3)) ∈ cdrF := by
    have := hTa.2.2; rwa [val_map_triple lab huv (Ne.symm hua) (Ne.symm hva)] at this
  have hFb : ({lab u, lab v, lab b} : Multiset (Fin 3)) ∈ cdrF := by
    have := hTb.2.2; rwa [val_map_triple lab huv (Ne.symm hub) (Ne.symm hvb)] at this
  have hc := hinges_card_ge lab hab huv hua hva hub hvb hFa hFb
  simp only at hc
  have hX0 := card_class_sdiff lab u v a b (lab u)
  have hY0 := card_class_sdiff lab u v a b (lab v)
  generalize ((univ.filter fun w => lab w = lab u) \ {u, v, a, b}) = X at hc hX0
  generalize ((univ.filter fun w => lab w = lab v) \ {u, v, a, b}) = Y at hc hY0
  have hX : Fintype.card V ≤ 4 * X.card + 8 := by have := hcls (lab u); omega
  have hY : Fintype.card V ≤ 4 * Y.card + 8 := by have := hcls (lab v); omega
  have hY1 : 1 ≤ Y.card := by omega
  have hle : X.card ≤ X.card * Y.card := Nat.le_mul_of_pos_right _ hY1
  have hcR : ((X.card : ℝ) * Y.card - X.card) ≤ (hinges (cHost lab) cdrF u v a b 6).card := by
    have : ((X.card * Y.card - X.card : ℕ) : ℝ) ≤ (hinges (cHost lab) cdrF u v a b 6).card := by
      exact_mod_cast hc
    rwa [Nat.cast_sub hle, Nat.cast_mul] at this
  have hNR : (400 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  have hXR : (Fintype.card V : ℝ) ≤ 4 * X.card + 8 := by exact_mod_cast hX
  have hYR : (Fintype.card V : ℝ) ≤ 4 * Y.card + 8 := by exact_mod_cast hY
  norm_num only [Nat.reduceSub]
  refine le_trans ?_ hcR
  have k1 : ((Fintype.card V : ℝ) - 8) / 4 ≤ X.card := by linarith
  have k2 : ((Fintype.card V : ℝ) - 12) / 4 ≤ (Y.card : ℝ) - 1 := by linarith
  have k3 := mul_le_mul k1 k2 (by linarith) (by linarith)
  nlinarith

end HingeCond

/-! ### The CDR host -/

/-- **H4** for the CDR host: `α = 1/32`, `h = 6`, for `n ≥ 400`. -/
theorem cdr_H4 {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c) :
    HingeCond (cdrHost a b c) cdrF (1 / 32) 6 := by
  obtain ⟨ha, hb, hc⟩ := class_lower_all h hn
  refine hingeCond_of (col3 a b c) (by rw [Fintype.card_fin]; exact hn) fun k => ?_
  rw [Fintype.card_fin, csz_col3]
  fin_cases k <;> simpa

/-- **H3** for the CDR host with the common constant `α = 1/32`. -/
theorem cdr_H3' {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c) :
    CommonNbrCond (cdrHost a b c) cdrF (1 / 32) := by
  intro u v huv k hk
  have := cdr_H3 h hn u v huv k hk
  have h0 : (0 : ℝ) ≤ Fintype.card (Fin (a + b + c)) := by positivity
  linarith

end CDRBicolour.Absorption
