/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.Reserve

/-!
# Octahedral hinges from a universal reserve

Choose the two free vertices in the reserve, with the colours of the two edge
roots. All seven core edges touch the reserve and survive. Removing the four
roots loses at most four candidates in either colour; excluding the diagonal
loses at most one candidate per first vertex. Thus reserve classes of size at
least `δR*n`, with `δR*n ≥ 10`, give `(δR^2/4)n^2` hinges of order six.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption

section Universal

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
variable {lab : V → Fin k} {L : Finset (Sym2 V)} (R : Finset V)
variable (hR : ∀ x ∈ R, ∀ v, x ≠ v → (rG L).Adj x v)

include hR

theorem reserve_hinges_card_ge {u v a b : V} (hab : a ≠ b)
    (hTa : IsAllowed (rHostK lab L) (bicF k) {u, v, a})
    (hTb : IsAllowed (rHostK lab L) (bicF k) {u, v, b}) :
    let X := (R.filter fun w => lab w = lab u) \ {u, v, a, b}
    let Y := (R.filter fun w => lab w = lab v) \ {u, v, a, b}
    X.card * Y.card - X.card ≤ (hinges (rHostK lab L) (bicF k) u v a b 6).card := by
  intro X Y
  obtain ⟨huv, hua, hva⟩ := ne_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := ne_of_card_three hTb.1
  have hFa : ({lab u, lab v, lab a} : Multiset (Fin k)) ∈ bicF k := by
    have hf := hTa.2.2
    rwa [val_map_triple lab huv hua.symm hva.symm] at hf
  have hFb : ({lab u, lab v, lab b} : Multiset (Fin k)) ∈ bicF k := by
    have hf := hTb.2.2
    rwa [val_map_triple lab huv hub.symm hvb.symm] at hf
  have memX : ∀ x ∈ X, x ∈ R ∧ lab x = lab u ∧ x ≠ u ∧ x ≠ v ∧ x ≠ a ∧ x ≠ b := by
    intro x hx
    simp only [X, mem_sdiff, mem_filter, mem_insert, mem_singleton] at hx
    tauto
  have memY : ∀ y ∈ Y, y ∈ R ∧ lab y = lab v ∧ y ≠ u ∧ y ≠ v ∧ y ≠ a ∧ y ≠ b := by
    intro y hy
    simp only [Y, mem_sdiff, mem_filter, mem_insert, mem_singleton] at hy
    tauto
  let P := (X ×ˢ Y).filter fun p : V × V => p.1 ≠ p.2
  have hsix : ∀ p ∈ P, Six u v a b p.1 p.2 := by
    intro p hp
    obtain ⟨hprod, hxy⟩ := mem_filter.mp hp
    obtain ⟨hx, hy⟩ := mem_product.mp hprod
    obtain ⟨-, -, xu, xv, xa, xb⟩ := memX _ hx
    obtain ⟨-, -, yu, yv, ya, yb⟩ := memY _ hy
    exact ⟨huv, hua, hub, xu.symm, yu.symm, hva, hvb, xv.symm, yv.symm, hab,
      xa.symm, ya.symm, xb.symm, yb.symm, hxy⟩
  have hsub : P.image (fun p => hcore u v a b p.1 p.2) ⊆
      hinges (rHostK lab L) (bicF k) u v a b 6 := by
    intro J hJ
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hJ
    have hprod := (mem_filter.mp hp).1
    have hx := memX _ (mem_product.mp hprod).1
    have hy := memY _ (mem_product.mp hprod).2
    have hxy := (mem_filter.mp hp).2
    simp only [hinges, mem_filter, mem_univ, true_and]
    refine ⟨hcore_isHingeRK (hsix p hp) hx.2.1 hy.2.1 hFa hFb
      (hTa.2.1 u (by simp) a (by simp) hua)
      (hTa.2.1 v (by simp) a (by simp) hva)
      (hTb.2.1 u (by simp) b (by simp) hub)
      (hTb.2.1 v (by simp) b (by simp) hvb)
      (hR p.2 hy.1 u hy.2.2.1).symm (hR p.1 hx.1 v hx.2.2.2.1)
      (hR p.1 hx.1 p.2 hxy) (hR p.1 hx.1 a hx.2.2.2.2.1)
      (hR p.1 hx.1 b hx.2.2.2.2.2) (hR p.2 hy.1 a hy.2.2.2.2.1)
      (hR p.2 hy.1 b hy.2.2.2.2.2), support_hcore (hsix p hp)⟩
  have hinj : Set.InjOn (fun p : V × V => hcore u v a b p.1 p.2) P := by
    intro p hp q hq he
    obtain ⟨h1, h2⟩ := hcore_inj (hsix p hp) (hsix q hq) he
    exact Prod.ext h1 h2
  have hcardP : #X * #Y - #X ≤ #P := by
    have hsplit : #P + #((X ×ˢ Y).filter fun p : V × V => ¬ p.1 ≠ p.2) = #(X ×ˢ Y) :=
      card_filter_add_card_filter_not _
    have hdiag : #((X ×ˢ Y).filter fun p : V × V => ¬ p.1 ≠ p.2) ≤ #X := by
      apply card_le_card_of_injOn (fun p => p.1)
      · intro p hp
        exact (mem_product.mp (mem_filter.mp hp).1).1
      · intro p hp q hq he
        have hp2 := (mem_filter.mp hp).2
        have hq2 := (mem_filter.mp hq).2
        simp only [ne_eq, not_not] at hp2 hq2
        exact Prod.ext he (by rw [← hp2, ← hq2]; exact he)
    rw [card_product] at hsplit
    omega
  exact hcardP.trans ((card_image_of_injOn hinj).symm.le.trans (card_le_card hsub))

theorem universal_reserve_H4 {δR : ℝ} (hδ : 0 < δR)
    (hcls : ∀ X, δR * Fintype.card V ≤ #(R.filter fun v => lab v = X))
    (h10 : 10 ≤ δR * Fintype.card V) :
    HingeCond (rHostK lab L) (bicF k) (δR ^ 2 / 4) 6 := by
  intro u v a b hab hTa0 hTb0
  refine ⟨6, le_rfl, le_rfl, ?_⟩
  have hTa : IsAllowed (rHostK lab L) (bicF k) {u, v, a} := by convert hTa0
  have hTb : IsAllowed (rHostK lab L) (bicF k) {u, v, b} := by convert hTb0
  have hc := reserve_hinges_card_ge R hR hab hTa hTb
  simp only at hc
  have bound : ∀ Z, #(R.filter fun w => lab w = Z) ≤
      #((R.filter fun w => lab w = Z) \ {u, v, a, b}) + 4 := by
    intro Z
    have h1 := le_card_sdiff ({u, v, a, b} : Finset V) (R.filter fun w => lab w = Z)
    have h2 := card_le_four (a := u) (b := v) (c := a) (d := b)
    omega
  have hX0 := bound (lab u)
  have hY0 := bound (lab v)
  generalize ((R.filter fun w => lab w = lab u) \ {u, v, a, b}) = X at hc hX0
  generalize ((R.filter fun w => lab w = lab v) \ {u, v, a, b}) = Y at hc hY0
  let n : ℝ := Fintype.card V
  have hXR : δR * n ≤ (#X : ℝ) + 4 := by
    have h := hcls (lab u)
    have hcast : (#(R.filter fun w => lab w = lab u) : ℝ) ≤ #X + 4 := by exact_mod_cast hX0
    linarith
  have hYR : δR * n ≤ (#Y : ℝ) + 4 := by
    have h := hcls (lab v)
    have hcast : (#(R.filter fun w => lab w = lab v) : ℝ) ≤ #Y + 4 := by exact_mod_cast hY0
    linarith
  have hY1 : 1 ≤ #Y := by
    have : (6 : ℝ) ≤ #Y := by linarith
    exact_mod_cast (by linarith : (1 : ℝ) ≤ #Y)
  have hle : #X ≤ #X * #Y := Nat.le_mul_of_pos_right _ hY1
  have hcR : (#X : ℝ) * #Y - #X ≤ #(hinges (rHostK lab L) (bicF k) u v a b 6) := by
    have hcast : ((#X * #Y - #X : ℕ) : ℝ) ≤
        #(hinges (rHostK lab L) (bicF k) u v a b 6) := by exact_mod_cast hc
    rwa [Nat.cast_sub hle, Nat.cast_mul] at hcast
  norm_num only [Nat.reduceSub]
  refine le_trans ?_ hcR
  have k1 : δR * n / 2 ≤ #X := by linarith
  have k2 : δR * n / 2 ≤ (#Y : ℝ) - 1 := by linarith
  have k3 := mul_le_mul k1 k2 (by positivity) (by linarith)
  nlinarith

end Universal

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}

theorem residual_H4_of_reserve (h : Setup lab κ g t) {S : Finset (Finset (Fin g))}
    (hS : _root_.STS.IsSTS S) (Λ : LFam A S t) {δR : ℝ} (hδ : 0 < δR)
    (hcls : ∀ X, δR * n ≤ #((reserve h).filter fun v => lab v = X))
    (h10 : 10 ≤ δR * n) :
    HingeCond (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) (δR ^ 2 / 4) 6 :=
  universal_reserve_H4 (reserve h) (fun x hx v hne => reserve_adj h hS Λ hx hne) hδ
    (by simpa only [Fintype.card_fin] using hcls) (by simpa only [Fintype.card_fin] using h10)

end CDRBicolour.KBicolor.Wilson
