/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Plantholt.Core

/-!
# Plantholt 2004, proof of Theorem 1.2: the cases of the inductive step

The induction is on `D − δ'`, where every degree lies between `δ'` and `D` (the paper inducts on
`Δ − δ`; working with bounds makes the reductions uniform). In each case a matching (or three)
is removed and the induction hypothesis applies.
-/

@[expose] public section

namespace Plantholt

open SimpleGraph Finset
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The hypotheses of the inductive statement. -/
def Good (c : ℝ) (G : SimpleGraph V) (D δ' : ℕ) : Prop :=
  (∀ v, G.degree v ≤ D) ∧ (∀ v, δ' ≤ G.degree v) ∧
    2 * c * Fintype.card V ≤ 3 * (δ' : ℝ) - D ∧ NoOverfull G D

/-- The induction hypothesis. -/
def IndHyp (V : Type*) [Fintype V] [DecidableEq V] (c : ℝ) (m : ℕ) : Prop :=
  ∀ (G : SimpleGraph V) (D δ' : ℕ), D - δ' < m → Good c G D δ' → G.lineGraph.Colorable D

/-- The context of the inductive step. -/
structure Ctx (c : ℝ) (G : SimpleGraph V) (D δ0 : ℕ) : Prop where
  hev : Even (Fintype.card V)
  good : Good c G D δ0
  hN : 3 * Fintype.card V + 2 * D ≤ 6 * δ0
  hcn : c * Fintype.card V ≤ δ0
  hD1 : D + 1 ≤ Fintype.card V
  hn4 : 4 ≤ Fintype.card V
  hδ : Fintype.card V + 2 ≤ 2 * δ0
  hδD : δ0 ≤ D
  ih : IndHyp V c (D - δ0)
  hC : ∀ (H : SimpleGraph V) (d : ℕ), (∀ v, H.degree v = d) → c * Fintype.card V ≤ d →
    H.lineGraph.Colorable d

variable {c : ℝ} {G : SimpleGraph V} {D δ0 : ℕ}

theorem Ctx.hmax (X : Ctx c G D δ0) : ∀ v, G.degree v ≤ D := X.good.1
theorem Ctx.hmin (X : Ctx c G D δ0) : ∀ v, δ0 ≤ G.degree v := X.good.2.1
theorem Ctx.hno (X : Ctx c G D δ0) : NoOverfull G D := X.good.2.2.2

theorem Ctx.h4 (X : Ctx c G D δ0) : 3 * Fintype.card V ≤ 4 * δ0 := by
  have := X.hδD; have := X.hN; omega

/-- Remove one matching and recurse with `D − 1`. -/
theorem step_one (X : Ctx c G D δ0) {M : SimpleGraph V} {W : Finset V}
    (hM : IsMatchingOn G M W) (hlt : δ0 < D) (hmax' : ∀ v, (G \ M).degree v ≤ D - 1)
    (hmin' : ∀ v, δ0 ≤ (G \ M).degree v) (hno : NoOverfull (G \ M) (D - 1)) :
    G.lineGraph.Colorable D := by
  have hcond := X.good.2.2.1
  have hc := X.ih (G \ M) (D - 1) δ0 (by omega) ⟨hmax', hmin', ?_, hno⟩
  · have := colorable_succ_of_matching G hM.1 hM.degree_le_one hc
    rwa [Nat.sub_add_cancel (by omega)] at this
  · push_cast [show 1 ≤ D by omega]
    linarith

theorem two_mul_sub_two {D n : ℕ} (hD : 1 ≤ D) : (D - 1) * (n - 2) + (n - 2) = D * (n - 2) := by
  rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hD]

theorem mem_erase_erase {x y v : V} :
    v ∈ (univ.erase x).erase y ↔ v ≠ x ∧ v ≠ y := by
  simp only [mem_erase, mem_univ, and_true]; tauto

theorem card_erase_erase {x y : V} (hxy : x ≠ y) :
    #((univ.erase x).erase y) = Fintype.card V - 2 := by
  rw [card_erase_of_mem (mem_erase.2 ⟨hxy.symm, mem_univ y⟩), card_erase_of_mem (mem_univ x),
    card_univ]
  omega

theorem card_compl_erase_erase {x y : V} (hxy : x ≠ y) : #((univ.erase x).erase y)ᶜ = 2 := by
  have h := card_add_card_compl ((univ.erase x).erase y)
  rw [card_erase_erase hxy] at h
  have : 2 ≤ Fintype.card V := by
    have := card_le_univ ({x, y} : Finset V)
    rw [card_pair hxy] at this; exact this
  omega

/-- **Removing a matching that misses two vertices `x, y`** (Case 1 and Subcase 1). -/
theorem remove_two (X : Ctx c G D δ0) {x y : V} (hxy : x ≠ y) (hx : G.degree x < D)
    (hy : G.degree y < D) (hz : ∀ z, z ≠ x → z ≠ y → δ0 + 1 ≤ G.degree z)
    (hb : ∀ z, z ≠ x → z ≠ y →
      dsum G + 2 ≤ 2 * G.degree z + D * (Fintype.card V - 2))
    (hbx : dsum G ≤ 2 * G.degree x + D * (Fintype.card V - 2))
    (hby : dsum G ≤ 2 * G.degree y + D * (Fintype.card V - 2)) :
    G.lineGraph.Colorable D := by
  set W := (univ.erase x).erase y with hW
  have hWc := card_compl_erase_erase hxy
  have hWn := card_erase_erase hxy
  have hev := X.hev
  have hδ := X.hδ
  obtain ⟨M, hM⟩ := exists_matchingOn G (W := W) (by
      rw [hWn]; rcases hev with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩)
    (fun v _ => by
      have h1 := deg_le_nbIn_add G W v
      have h2 := X.hmin v
      rw [hWn]; rw [hWc] at h1; omega)
  have hmemW : ∀ v, v ∈ W ↔ v ≠ x ∧ v ≠ y := fun v => mem_erase_erase
  have hmax' : ∀ v, (G \ M).degree v ≤ D - 1 := by
    intro v
    by_cases hv : v ∈ W
    · have := deg_sdiff_mem hM hv; have := X.hmax v; omega
    · rw [deg_sdiff_not_mem hM hv]
      rw [hmemW] at hv
      by_cases hvx : v = x
      · subst hvx; omega
      · have : v = y := by tauto
        subst this; omega
  have hmin' : ∀ v, δ0 ≤ (G \ M).degree v := by
    intro v
    by_cases hv : v ∈ W
    · have := deg_sdiff_mem hM hv; have := hz v ((hmemW v).1 hv).1 ((hmemW v).1 hv).2; omega
    · rw [deg_sdiff_not_mem hM hv]; exact X.hmin v
  have hds := dsum_sdiff hM
  rw [hWn] at hds
  have hsub := two_mul_sub_two (n := Fintype.card V) (show 1 ≤ D by omega)
  have hno : NoOverfull (G \ M) (D - 1) := by
    refine noOverfull_of_erase (G \ M) hev hmax' hmin' (by have := X.hD1; omega) hδ fun w => ?_
    by_cases hw : w ∈ W
    · have := deg_sdiff_mem hM hw
      have := hb w ((hmemW w).1 hw).1 ((hmemW w).1 hw).2
      omega
    · rw [deg_sdiff_not_mem hM hw]
      rw [hmemW] at hw
      by_cases hwx : w = x
      · subst hwx; omega
      · have : w = y := by tauto
        subst this; omega
  have hlt : δ0 < D := (X.hmin x).trans_lt hx
  exact step_one X hM hlt hmax' hmin' hno

/-- **Case 1**: `G` has a `D`-full set. -/
theorem case_full (X : Ctx c G D δ0) {S : Finset V} (hS : IsFull G D S)
    (hnr : ∃ v, G.degree v < D) : G.lineGraph.Colorable D := by
  have hcard := card_add_one_of_full G X.hev X.hmax X.hmin X.hD1 X.hδ hS
  set n := Fintype.card V with hn
  obtain ⟨x, hx⟩ : ∃ x, x ∉ S := by
    by_contra hall
    push_neg at hall
    have : #S = n := by rw [hn, ← card_univ]; congr 1; exact eq_univ_of_forall hall
    omega
  have hSeq : S = univ.erase x := by
    apply eq_of_subset_of_card_le
    · intro v hv; exact mem_erase.2 ⟨fun h => hx (h ▸ hv), mem_univ v⟩
    · rw [card_erase_of_mem (mem_univ x), card_univ]; omega
  subst hSeq
  have hfull := hS.2.2
  rw [card_erase_of_mem (mem_univ x), card_univ, show n - 1 - 1 = n - 2 by omega] at hfull
  have hodd : ∀ w : V, Odd #(univ.erase w) := fun w => by
    rw [card_erase_of_mem (mem_univ w), card_univ]
    rcases X.hev with ⟨t, ht⟩; exact ⟨t - 1, by have := X.hn4; omega⟩
  have hno' : ∀ w : V, 2 * eIn G (univ.erase w) ≤ D * (n - 2) := fun w => by
    have := X.hno _ (hodd w)
    rwa [card_erase_of_mem (mem_univ w), card_univ, show n - 1 - 1 = n - 2 by omega] at this
  have hsum : dsum G = D * (n - 2) + 2 * G.degree x := by
    have := two_mul_eIn_erase G x; have := hno' x; omega
  have hxmin : ∀ w, G.degree x ≤ G.degree w := fun w => by
    have := two_mul_eIn_erase G w; have := hno' w; omega
  obtain ⟨v₀, hv₀⟩ := hnr
  have hxD : G.degree x < D := (hxmin v₀).trans_lt hv₀
  have hdfc : dfc G D = 2 * (D - G.degree x) := by
    have h1 := dfc_add_dsum G X.hmax
    have h2 := mul_sub_two (D := D) (show 2 ≤ n by have := X.hn4; omega)
    rw [← hn] at h1
    omega
  have hrest : ∑ v ∈ univ.erase x, (D - G.degree v) = D - G.degree x := by
    have := dfc_erase G (D := D) x; omega
  obtain ⟨v₁, hv₁x, hv₁⟩ := exists_lt_of_dfc G (D := D) x (by omega)
  obtain ⟨y, hy, hymin⟩ := (univ.erase x).exists_min_image (fun v => G.degree v)
    ⟨v₁, mem_erase.2 ⟨hv₁x, mem_univ _⟩⟩
  have hyx : y ≠ x := ne_of_mem_erase hy
  have hyD : G.degree y < D := (hymin v₁ (mem_erase.2 ⟨hv₁x, mem_univ _⟩)).trans_lt hv₁
  have hz : ∀ z, z ≠ x → z ≠ y → G.degree x + 1 ≤ G.degree z := by
    intro z hzx hzy
    by_contra hlt
    have hyz := hymin z (mem_erase.2 ⟨hzx, mem_univ _⟩)
    have := dfc_ge_three G (D := D) hyx.symm hzx.symm (Ne.symm hzy)
    have := hxmin y
    omega
  refine remove_two X hyx.symm hxD hyD (fun z h1 h2 => ?_) (fun z h1 h2 => ?_)
    (by rw [← hn]; omega) ?_
  · have := hz z h1 h2; have := X.hmin x; omega
  · rw [← hn]; have := hz z h1 h2; omega
  · rw [← hn]; have := hxmin y; omega

end Plantholt
