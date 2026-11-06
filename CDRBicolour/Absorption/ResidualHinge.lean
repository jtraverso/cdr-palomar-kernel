/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.ResidualLattice
public import CDRBicolour.Absorption.Hinge

/-!
# H3, H4 and density for residual hosts (backlog item 2a)

`G = K_n - L` where every point lies on at most `Δ` edges of `L` (`degL L p ≤ Δ`).  If every
class has at least `(N + 8)/4` points and `64 Δ + 64 ≤ N`:

* `bigR_of_deg`: the density condition `BigR` used for H2;
* `residual_H3`: `CommonNbrCond` with `α = 1/32`;
* `residual_H4`: `HingeCond` with `α = 1/32`, `h = 6` (the octahedral hinges of the complete
  case, with `x` and `y` chosen adjacent in `G` to everything they meet).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

section Residual

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3} {L : Finset (Sym2 V)}

/-- The `L`-neighbours of `p`. -/
def nbL (L : Finset (Sym2 V)) (p : V) : Finset V := univ.filter fun w => s(w, p) ∈ L

/-- The `L`-degree of `p`. -/
def degL (L : Finset (Sym2 V)) (p : V) : ℕ := #(nbL L p)

theorem adj_of_not_nbL {w p : V} (hne : w ≠ p) (h : w ∉ nbL L p) : (rG L).Adj w p := by
  rw [rG_adj]
  refine ⟨fun hw => h ?_, hne⟩
  simp [nbL, hw]

/-- Points of class `k` avoiding a finite set `B` and the `L`-neighbourhoods of `B`. -/
theorem card_good (k : Fin 3) (B : Finset V) {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ) :
    csz lab k ≤ #((univ.filter fun w => lab w = k) \ (B ∪ B.biUnion (nbL L))) +
      #B * (Δ + 1) := by
  have h1 := le_card_sdiff (B ∪ B.biUnion (nbL L)) (univ.filter fun w => lab w = k)
  have h2 : #(B ∪ B.biUnion (nbL L)) ≤ #B * (Δ + 1) := by
    calc #(B ∪ B.biUnion (nbL L)) ≤ #B + #(B.biUnion (nbL L)) := card_union_le _ _
      _ ≤ #B + ∑ p ∈ B, #(nbL L p) := by gcongr; exact card_biUnion_le
      _ ≤ #B + ∑ _p ∈ B, Δ := by gcongr with p; exact hdeg p
      _ = #B * (Δ + 1) := by rw [sum_const, smul_eq_mul]; ring
  unfold csz
  omega

theorem mem_good {k : Fin 3} {B : Finset V} {w : V}
    (hw : w ∈ (univ.filter fun w => lab w = k) \ (B ∪ B.biUnion (nbL L))) :
    lab w = k ∧ ∀ p ∈ B, (rG L).Adj w p := by
  simp only [mem_sdiff, mem_filter, mem_univ, true_and, mem_union, mem_biUnion, not_or,
    not_exists, not_and] at hw
  refine ⟨hw.1, fun p hp => adj_of_not_nbL (fun h => hw.2.1 (h ▸ hp)) (hw.2.2 p hp)⟩

/-- **Density** from a degree bound. -/
theorem bigR_of_deg {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ) (hcls : ∀ k, 4 * (Δ + 1) < csz lab k) :
    BigR lab L := by
  intro k p q r s
  set B : Finset V := {p, q, r, s}
  have hB : #B ≤ 4 := card_le_four
  have hc := card_good (lab := lab) k B hdeg
  have hlt := hcls k
  have : 0 < #((univ.filter fun w => lab w = k) \ (B ∪ B.biUnion (nbL L))) := by
    have : #B * (Δ + 1) ≤ 4 * (Δ + 1) := Nat.mul_le_mul_right _ hB
    omega
  obtain ⟨w, hw⟩ := card_pos.mp this
  obtain ⟨hl, ha⟩ := mem_good hw
  exact ⟨w, hl, ha p (by simp [B]), ha q (by simp [B]), ha r (by simp [B]), ha s (by simp [B])⟩

/-- **H3** for the residual host. -/
theorem residual_H3 {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ)
    (hcls : ∀ k, Fintype.card V + 8 ≤ 4 * csz lab k) (hΔ : 64 * Δ + 64 ≤ Fintype.card V) :
    CommonNbrCond (rHost lab L) cdrF (1 / 32) := by
  intro u v _ k _
  set B : Finset V := {u, v}
  have hB : #B ≤ 2 := card_le_two
  have hc := card_good (lab := lab) k B hdeg
  have hsub : (univ.filter fun w => lab w = k) \ (B ∪ B.biUnion (nbL L)) ⊆
      commonNbrs (rHost lab L) k u v := by
    intro w hw
    obtain ⟨hl, ha⟩ := mem_good hw
    simp only [commonNbrs, mem_filter, mem_univ, true_and]
    exact ⟨(ha u (by simp [B])).symm, (ha v (by simp [B])).symm, hl⟩
  have hle := card_le_card hsub
  have hk := hcls k
  have : #B * (Δ + 1) ≤ 2 * (Δ + 1) := Nat.mul_le_mul_right _ hB
  have hnat : Fintype.card V ≤ 32 * #(commonNbrs (rHost lab L) k u v) := by omega
  have : (Fintype.card V : ℝ) ≤ 32 * #(commonNbrs (rHost lab L) k u v) := by exact_mod_cast hnat
  linarith

theorem mem_edges_rHost {p q : V} : s(p, q) ∈ edges (rHost lab L) ↔ (rG L).Adj p q := by
  simp [edges]

theorem isDecomposition_three' (H : Host V (Fin 3)) {T1 T2 T3 : Finset V} {J : Finset (Sym2 V)}
    (h1 : IsAllowed H cdrF T1) (h2 : IsAllowed H cdrF T2)
    (h3 : IsAllowed H cdrF T3) (d12 : Disjoint (triEdges T1) (triEdges T2))
    (d13 : Disjoint (triEdges T1) (triEdges T3)) (d23 : Disjoint (triEdges T2) (triEdges T3))
    (hcov : triEdges T1 ∪ triEdges T2 ∪ triEdges T3 = J) :
    IsDecomposition H cdrF J {T1, T2, T3} := by
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

set_option maxHeartbeats 2000000 in
/-- The octahedral hinge in the residual host. -/
theorem hcore_isHingeR {u v a b x y : V} (h : Six u v a b x y)
    (hlx : lab x = lab u) (hly : lab y = lab v)
    (hFa : ({lab u, lab v, lab a} : Multiset (Fin 3)) ∈ cdrF)
    (hFb : ({lab u, lab v, lab b} : Multiset (Fin 3)) ∈ cdrF)
    (Aua : (rG L).Adj u a) (Ava : (rG L).Adj v a) (Aub : (rG L).Adj u b) (Avb : (rG L).Adj v b)
    (Auy : (rG L).Adj u y) (Axv : (rG L).Adj x v) (Axy : (rG L).Adj x y) (Axa : (rG L).Adj x a)
    (Axb : (rG L).Adj x b) (Aya : (rG L).Adj y a) (Ayb : (rG L).Adj y b) :
    IsHinge (rHost lab L) cdrF u v a b (hcore u v a b x y) := by
  obtain ⟨uv, ua, ub, ux, uy, va, vb, vx, vy, ab, ax, ay, bx, by', xy⟩ := h
  have vu := uv.symm; have au := ua.symm; have bu := ub.symm; have xu := ux.symm
  have yu := uy.symm; have av := va.symm; have bv := vb.symm; have xv := vx.symm
  have yv := vy.symm; have ba := ab.symm; have xa := ax.symm; have ya := ay.symm
  have xb := bx.symm; have yb := by'.symm; have yx := xy.symm
  have A1 : IsAllowed (rHost lab L) cdrF {u, y, a} :=
    isAllowed_tripleR Auy Aua Aya (by rw [hly]; exact hFa)
  have A2 : IsAllowed (rHost lab L) cdrF {x, v, a} :=
    isAllowed_tripleR Axv Axa Ava (by rw [hlx]; exact hFa)
  have A3 : IsAllowed (rHost lab L) cdrF {x, y, b} :=
    isAllowed_tripleR Axy Axb Ayb (by rw [hlx, hly]; exact hFb)
  have B1 : IsAllowed (rHost lab L) cdrF {u, y, b} :=
    isAllowed_tripleR Auy Aub Ayb (by rw [hly]; exact hFb)
  have B2 : IsAllowed (rHost lab L) cdrF {x, v, b} :=
    isAllowed_tripleR Axv Axb Avb (by rw [hlx]; exact hFb)
  have B3 : IsAllowed (rHost lab L) cdrF {x, y, a} :=
    isAllowed_tripleR Axy Axa Aya (by rw [hlx, hly]; exact hFa)
  refine ⟨?_, ?_, ⟨{{u, y, a}, {x, v, a}, {x, y, b}}, ?_⟩,
    ⟨{{u, y, b}, {x, v, b}, {x, y, a}}, ?_⟩⟩
  · intro e he
    simp only [hcore, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [mem_edges_rHost] <;> assumption
  · clear Aua Ava Aub Avb Auy Axv Axy Axa Axb Aya Ayb A1 A2 A3 B1 B2 B3
    rw [disjoint_left]
    intro e he he'
    simp only [hcore, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [triEdges, mem_union, mem_filter, mk_mem_sym2_iff, mem_insert, mem_singleton,
        Sym2.mk_isDiag_iff] at he' <;> simp_all
  · clear Aua Ava Aub Avb Auy Axv Axy Axa Axb Aya Ayb
    refine isDecomposition_three' _ A1 A2 A3 ?_ ?_ ?_ ?_
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
  · clear Aua Ava Aub Avb Auy Axv Axy Axa Axb Aya Ayb
    refine isDecomposition_three' _ B1 B2 B3 ?_ ?_ ?_ ?_
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

/-- **H4** for the residual host. -/
theorem residual_H4 {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ)
    (hcls : ∀ k, Fintype.card V + 8 ≤ 4 * csz lab k) (hΔ : 64 * Δ + 64 ≤ Fintype.card V) :
    HingeCond (rHost lab L) cdrF (1 / 32) 6 := by
  intro u v a b hab hTa0 hTb0
  refine ⟨6, le_rfl, le_rfl, ?_⟩
  have hTa : IsAllowed (rHost lab L) cdrF ({u, v, a} : Finset V) := by convert hTa0
  have hTb : IsAllowed (rHost lab L) cdrF ({u, v, b} : Finset V) := by convert hTb0
  obtain ⟨huv, hua, hva⟩ := ne_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := ne_of_card_three hTb.1
  have adjA : ∀ p ∈ ({u, v, a} : Finset V), ∀ q ∈ ({u, v, a} : Finset V), p ≠ q →
      (rG L).Adj p q := hTa.2.1
  have adjB : ∀ p ∈ ({u, v, b} : Finset V), ∀ q ∈ ({u, v, b} : Finset V), p ≠ q →
      (rG L).Adj p q := hTb.2.1
  have Aua : (rG L).Adj u a := adjA u (by simp) a (by simp) hua
  have Ava : (rG L).Adj v a := adjA v (by simp) a (by simp) hva
  have Aub : (rG L).Adj u b := adjB u (by simp) b (by simp) hub
  have Avb : (rG L).Adj v b := adjB v (by simp) b (by simp) hvb
  have hFa : ({lab u, lab v, lab a} : Multiset (Fin 3)) ∈ cdrF := by
    have : ({u, v, a} : Finset V).val.map lab ∈ cdrF := hTa.2.2
    rwa [val_map_triple lab huv (Ne.symm hua) (Ne.symm hva)] at this
  have hFb : ({lab u, lab v, lab b} : Multiset (Fin 3)) ∈ cdrF := by
    have : ({u, v, b} : Finset V).val.map lab ∈ cdrF := hTb.2.2
    rwa [val_map_triple lab huv (Ne.symm hub) (Ne.symm hvb)] at this
  set B : Finset V := {u, v, a, b} with hBdef
  have hB : #B ≤ 4 := card_le_four
  set X := (univ.filter fun w => lab w = lab u) \ (B ∪ B.biUnion (nbL L)) with hX
  set Y := (univ.filter fun w => lab w = lab v) \ (B ∪ B.biUnion (nbL L)) with hY
  have memX : ∀ x ∈ X, lab x = lab u ∧ (∀ p ∈ B, (rG L).Adj x p) := fun x hx => mem_good hx
  have memY : ∀ y ∈ Y, lab y = lab v ∧ (∀ p ∈ B, (rG L).Adj y p) := fun y hy => mem_good hy
  set P := (X ×ˢ Y).filter fun p : V × V => p.2 ∉ insert p.1 (nbL L p.1) with hP
  have hgood : ∀ p ∈ P, Six u v a b p.1 p.2 ∧ lab p.1 = lab u ∧ lab p.2 = lab v ∧
      (rG L).Adj u p.2 ∧ (rG L).Adj p.1 v ∧ (rG L).Adj p.1 p.2 ∧ (rG L).Adj p.1 a ∧
      (rG L).Adj p.1 b ∧ (rG L).Adj p.2 a ∧ (rG L).Adj p.2 b := by
    rintro ⟨x, y⟩ hp
    simp only [hP, mem_filter, mem_product, mem_insert, not_or] at hp
    obtain ⟨⟨hx, hy⟩, hyx, hyn⟩ := hp
    obtain ⟨lx, ax⟩ := memX x hx
    obtain ⟨ly, ay⟩ := memY y hy
    have xu := ax u (by simp [B]); have xv := ax v (by simp [B])
    have xa := ax a (by simp [B]); have xb := ax b (by simp [B])
    have yu := ay u (by simp [B]); have yv := ay v (by simp [B])
    have ya := ay a (by simp [B]); have yb := ay b (by simp [B])
    have Axy : (rG L).Adj x y := (adj_of_not_nbL hyx hyn).symm
    exact ⟨⟨huv, hua, hub, xu.ne.symm, yu.ne.symm, hva, hvb, xv.ne.symm, yv.ne.symm, hab,
      xa.ne.symm, ya.ne.symm, xb.ne.symm, yb.ne.symm, Axy.ne⟩, lx, ly, yu.symm, xv, Axy, xa, xb,
      ya, yb⟩
  have hsub : P.image (fun p => hcore u v a b p.1 p.2) ⊆ hinges (rHost lab L) cdrF u v a b 6 := by
    intro J hJ
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hJ
    obtain ⟨h6, lx, ly, A1, A2, A3, A4, A5, A6, A7⟩ := hgood p hp
    simp only [hinges, mem_filter, mem_univ, true_and]
    exact ⟨hcore_isHingeR h6 lx ly hFa hFb Aua Ava Aub Avb A1 A2 A3 A4 A5 A6 A7, support_hcore h6⟩
  have hinj : Set.InjOn (fun p : V × V => hcore u v a b p.1 p.2) P := by
    intro p hp q hq he
    obtain ⟨h1, h2⟩ := hcore_inj (hgood p hp).1 (hgood q hq).1 he
    exact Prod.ext h1 h2
  -- counting
  have hfib : ∀ x ∈ X, #Y - (Δ + 1) ≤ #(Y.filter fun y => y ∉ insert x (nbL L x)) := by
    intro x _
    have h1 := le_card_sdiff (insert x (nbL L x)) Y
    have h2 : #(insert x (nbL L x)) ≤ Δ + 1 := (card_insert_le _ _).trans (by have := hdeg x; unfold degL at this; omega)
    have h3 : Y \ insert x (nbL L x) = Y.filter fun y => y ∉ insert x (nbL L x) := by
      ext y; simp
    rw [h3] at h1
    omega
  have hPcard : #X * (#Y - (Δ + 1)) ≤ #P := by
    have : #P = ∑ x ∈ X, #(Y.filter fun y => y ∉ insert x (nbL L x)) := by
      rw [hP, card_eq_sum_ones, sum_filter, sum_product]
      refine sum_congr rfl fun x _ => ?_
      rw [card_eq_sum_ones, sum_filter]
    rw [this, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum hfib
  have hXc := card_good (lab := lab) (lab u) B hdeg
  have hYc := card_good (lab := lab) (lab v) B hdeg
  rw [← hX] at hXc
  rw [← hY] at hYc
  have hBX : #B * (Δ + 1) ≤ 4 * (Δ + 1) := Nat.mul_le_mul_right _ hB
  have h1 := hcls (lab u)
  have h2 := hcls (lab v)
  set N := Fintype.card V
  have hXl : 3 * N + 32 ≤ 16 * #X := by omega
  have hYl : 11 * N + 128 ≤ 64 * (#Y - (Δ + 1)) := by omega
  have hNat : N * N ≤ 32 * #(hinges (rHost lab L) cdrF u v a b 6) := by
    have hcard := (card_image_of_injOn hinj).symm.le.trans (card_le_card hsub)
    have : 33 * (N * N) ≤ 1024 * (#X * (#Y - (Δ + 1))) := by
      have := Nat.mul_le_mul hXl hYl
      nlinarith
    omega
  have : ((N : ℝ) * N) ≤ 32 * #(hinges (rHost lab L) cdrF u v a b 6) := by exact_mod_cast hNat
  norm_num only [Nat.reduceSub]
  rw [pow_two]
  linarith

end Residual

end CDRBicolour.Absorption
