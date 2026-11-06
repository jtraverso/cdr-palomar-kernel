/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Plantholt.Cases

/-!
# Plantholt 2004, proof of Theorem 1.2: Case 2

No `D`-full set, and any two vertices of degree below `D` are adjacent. Then more than half of
the vertices have degree `D` (`card_high`), and a matching (or three, in Subcase 3) is removed.
-/

@[expose] public section

namespace Plantholt

open SimpleGraph Finset
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {c : ℝ} {G : SimpleGraph V} {D δ0 : ℕ}

/-- The vertices of degree `D`. -/
noncomputable def high (G : SimpleGraph V) (D : ℕ) : Finset V := univ.filter fun v => G.degree v = D

theorem mem_high {v : V} : v ∈ high G D ↔ G.degree v = D := by simp [high]

theorem high_arith {h k n D cb : ℕ} (hn : h + k = n) (hD : D + 1 ≤ n) (hD1 : 1 ≤ D) (hh : 1 ≤ h)
    (hk : 1 ≤ k)
    (hi : h * D ≤ cb + h * (h - 1)) (hlo : cb + k * (k - 1) ≤ k * (D - 1)) : k < h := by
  by_contra hkh
  push_neg at hkh
  have hi' : (h : ℤ) * D ≤ cb + h * (h - 1) := by exact_mod_cast hi
  have hlo' : (cb : ℤ) + k * (k - 1) ≤ k * (D - 1) := by exact_mod_cast hlo
  push_cast [hh, hk, hD1] at hi' hlo'
  have hn' : (h : ℤ) + k = n := by exact_mod_cast hn
  have hD' : (D : ℤ) + 1 ≤ n := by exact_mod_cast hD
  have h1 : (0 : ℤ) ≤ ((k : ℤ) - h) * ((n : ℤ) - D) := mul_nonneg (by omega) (by omega)
  have hh' : (1 : ℤ) ≤ h := by exact_mod_cast hh
  nlinarith

/-- **More than half of the vertices have degree `D`** (Case 2 of Plantholt). -/
theorem card_high (hmax : ∀ v, G.degree v ≤ D) (hD : D + 1 ≤ Fintype.card V)
    (hx0 : ∃ x, G.degree x = D)
    (hcomp : ∀ u v, u ≠ v → G.degree u < D → G.degree v < D → G.Adj u v) :
    Fintype.card V < 2 * #(high G D) := by
  set H := high G D
  have hcard := card_add_card_compl H
  obtain ⟨x, hx⟩ := hx0
  have hh : 1 ≤ #H := card_pos.2 ⟨x, mem_high.2 hx⟩
  rcases Nat.eq_zero_or_pos #Hᶜ with hk | hk
  · omega
  have hi : #H * D ≤ cob G H + #H * (#H - 1) := by
    rw [cob]
    calc #H * D = ∑ v ∈ H, G.degree v := by
          rw [sum_congr rfl fun v hv => mem_high.1 hv, sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ H, (#((G.neighborFinset v).filter (· ∉ H)) + (#H - 1)) :=
          sum_le_sum fun v hv => le_card_filter_not_mem G hv
      _ = _ := by rw [sum_add_distrib, sum_const, smul_eq_mul]
  have hlo : cob G H + #Hᶜ * (#Hᶜ - 1) ≤ #Hᶜ * (D - 1) := by
    rw [cob_eq_compl]
    calc ∑ u ∈ Hᶜ, #((G.neighborFinset u).filter (· ∈ H)) + #Hᶜ * (#Hᶜ - 1)
        = ∑ u ∈ Hᶜ, (#((G.neighborFinset u).filter (· ∈ H)) + (#Hᶜ - 1)) := by
          rw [sum_add_distrib, sum_const, smul_eq_mul]
      _ ≤ ∑ _u ∈ Hᶜ, (D - 1) := sum_le_sum fun u hu => by
          have hu' : G.degree u < D := by
            have := hmax u
            have : G.degree u ≠ D := fun h => (mem_compl.1 hu) (mem_high.2 h)
            omega
          have hsub : Hᶜ.erase u ⊆ (G.neighborFinset u).filter (· ∉ H) := by
            intro w hw
            obtain ⟨hwu, hw⟩ := mem_erase.1 hw
            have hw' : G.degree w < D := by
              have := hmax w
              have : G.degree w ≠ D := fun h => (mem_compl.1 hw) (mem_high.2 h)
              omega
            exact mem_filter.2 ⟨(mem_neighborFinset _ _ _).2 (hcomp u w hwu.symm hu' hw'),
              mem_compl.1 hw⟩
          have h1 := card_le_card hsub
          rw [card_erase_of_mem hu] at h1
          have h2 := card_filter_add_card_filter_not (s := G.neighborFinset u) (p := (· ∈ H))
          rw [card_neighborFinset_eq_degree] at h2
          omega
      _ = #Hᶜ * (D - 1) := by rw [sum_const, smul_eq_mul]
  have hD1 : 1 ≤ D := by
    obtain ⟨u, hu⟩ := card_pos.1 hk
    have := hmax u
    have : G.degree u ≠ D := fun h => (mem_compl.1 hu) (mem_high.2 h)
    omega
  have := high_arith hcard hD hD1 hh hk hi hlo
  omega

/-- Case 2 gives the strict vertex-deleted bound. -/
theorem case2_bound (X : Ctx c G D δ0) (hnf : ∀ S, ¬ IsFull G D S) (w : V) :
    dsum G + 2 ≤ 2 * G.degree w + D * (Fintype.card V - 2) := by
  have h1 := two_mul_eIn_erase G w
  have hcw : #(univ.erase w) = Fintype.card V - 1 := by rw [card_erase_of_mem (mem_univ w), card_univ]
  have hn4 := X.hn4
  obtain ⟨t, ht⟩ := X.hev
  have hnf' := hnf (univ.erase w)
  simp only [IsFull, hcw, not_and, not_le] at hnf'
  have hlt := hnf' (by omega) ⟨t - 1, by omega⟩
  rw [show Fintype.card V - 1 - 1 = Fintype.card V - 2 by omega] at hlt
  have hpar : D * (Fintype.card V - 2) = 2 * (D * (t - 1)) := by
    rw [show Fintype.card V - 2 = 2 * (t - 1) by omega]; ring
  rw [dsum_eq_two_mul] at h1 ⊢
  omega

/-- **Case 2, `D − δ = 1`**: remove a perfect matching of the vertices of degree `D`. -/
theorem case2_a (X : Ctx c G D δ0) (hhigh : Fintype.card V < 2 * #(high G D))
    (hall : ∀ v, D ≤ G.degree v + 1) (hnr : ∃ v, G.degree v < D) :
    G.lineGraph.Colorable D := by
  set H := high G D
  have hcard := card_add_card_compl H
  have hmax := X.hmax
  -- the number of vertices of degree `D − 1` is even
  have hdfc : dfc G D = #Hᶜ := by
    rw [dfc, ← sum_filter_add_sum_filter_not univ (· ∈ H)]
    have h0 : ∑ v ∈ univ.filter (· ∈ H), (D - G.degree v) = 0 :=
      sum_eq_zero fun v hv => by have := mem_high.1 (mem_filter.1 hv).2; omega
    have h1 : ∑ v ∈ univ.filter (· ∉ H), (D - G.degree v) = #(univ.filter (· ∉ H)) := by
      rw [card_eq_sum_ones]
      exact sum_congr rfl fun v hv => by
        have h1 : G.degree v ≠ D := fun h => (mem_filter.1 hv).2 (mem_high.2 h)
        have := hmax v; have := hall v; omega
    rw [h0, h1, zero_add]; congr 1; ext v; simp
  have hHev : Even #H := by
    have h1 := dfc_add_dsum G hmax
    rw [dsum_eq_two_mul, hdfc] at h1
    obtain ⟨t, ht⟩ := X.hev
    have hDn : D * Fintype.card V = 2 * (D * t) := by rw [show Fintype.card V = t + t from ht]; ring
    have hk : Even #Hᶜ := ⟨D * t - #G.edgeFinset, by omega⟩
    have hsum : Even (#H + #Hᶜ) := by rw [hcard]; exact ⟨t, ht⟩
    exact (Nat.even_add.1 hsum).2 hk
  have h4 := X.h4
  obtain ⟨M, hM⟩ := exists_matchingOn G (W := H) hHev fun v hv => by
    have h1 := deg_le_nbIn_add G H v
    rw [mem_high.1 hv] at h1
    have := X.hmin v
    have := X.hδD
    omega
  have hreg : ∀ v, (G \ M).degree v = D - 1 := by
    intro v
    by_cases hv : v ∈ H
    · have := deg_sdiff_mem hM hv; rw [mem_high.1 hv] at this; omega
    · rw [deg_sdiff_not_mem hM hv]
      have : G.degree v ≠ D := fun h => hv (mem_high.2 h)
      have := hmax v; have := hall v; omega
  obtain ⟨v₀, hv₀⟩ := hnr
  have hD1 : δ0 ≤ D - 1 := by have := X.hmin v₀; omega
  have hc := X.hC (G \ M) (D - 1) hreg (by
    have := X.hcn
    have h' : (δ0 : ℝ) ≤ ((D - 1 : ℕ) : ℝ) := by exact_mod_cast hD1
    linarith)
  have := colorable_succ_of_matching G hM.1 hM.degree_le_one hc
  rwa [Nat.sub_add_cancel (by omega)] at this

/-- **Removing a matching of a set `W ⊇ high`** with three vertices of minimum degree outside
(Subcase 2). -/
theorem remove_set (X : Ctx c G D δ0) {W : Finset V} {δa : ℕ} (hWev : Even #W)
    (hHW : high G D ⊆ W) (hδa : ∀ v, δa ≤ G.degree v) (hWL : ∀ v ∈ W, δa + 1 ≤ G.degree v)
    (hWbig : ∀ v ∈ W, 2 * Fintype.card V ≤ 2 * G.degree v + #W)
    {a b d : V} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (ha : G.degree a = δa)
    (hb : G.degree b = δa) (hd : G.degree d = δa) (hlt : δa < D) : G.lineGraph.Colorable D := by
  have hmax := X.hmax
  obtain ⟨M, hM⟩ := exists_matchingOn G (W := W) hWev fun v hv => by
    have h1 := deg_le_nbIn_add G W v
    have h2 := card_add_card_compl W
    have := hWbig v hv
    omega
  have hnotW : ∀ v, G.degree v = δa → v ∉ W := fun v hv hW => by
    have := hWL v hW; omega
  have hmax' : ∀ v, (G \ M).degree v ≤ D - 1 := by
    intro v
    by_cases hv : v ∈ W
    · have := deg_sdiff_mem hM hv; have := hmax v; omega
    · rw [deg_sdiff_not_mem hM hv]
      have : G.degree v ≠ D := fun h => hv (hHW (mem_high.2 h))
      have := hmax v; omega
  have hmina : ∀ v, δa ≤ (G \ M).degree v := by
    intro v
    by_cases hv : v ∈ W
    · have := deg_sdiff_mem hM hv; have := hWL v hv; omega
    · rw [deg_sdiff_not_mem hM hv]; exact hδa v
  have hδ0a : δ0 ≤ δa := by rw [← ha]; exact X.hmin a
  have hno : NoOverfull (G \ M) (D - 1) := by
    refine noOverfull_of_erase (G \ M) X.hev hmax' (fun v => hδ0a.trans (hmina v))
      (by have := X.hD1; omega) X.hδ fun w => ?_
    refine erase_bound_of_three (G \ M) hmax' hab had hbd (t := δa) ?_ ?_ ?_ hmina
      (by have := X.hn4; omega) w
    · rw [deg_sdiff_not_mem hM (hnotW a ha), ha]
    · rw [deg_sdiff_not_mem hM (hnotW b hb), hb]
    · rw [deg_sdiff_not_mem hM (hnotW d hd), hd]
  exact step_one X hM (hδ0a.trans_lt hlt) hmax' (fun v => hδ0a.trans (hmina v)) hno

end Plantholt
