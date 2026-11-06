/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexHingeRelativeTail
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Relative sampling concentration for a prescribed subfamily of physical
hinges. In particular the subfamily may exclude the edge between the apices. -/

open Finset Classical S07V24 TypedTriangle.SparseEdge
noncomputable section

namespace TypedTriangle.RawReference

theorem hinge_subfamily_tail_relative {V I : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {α q η : ℝ} {u v a b : V} {i : ℕ}
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b)
    (hi6 : 6 ≤ i) (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 0 < Fintype.card V)
    (Fam : Finset (Finset (Sym2 V)))
    (hFam : Fam ⊆ hinges G lab F u v a b i)
    (hcount : α * (Fintype.card V : ℝ) ^ (i - 4) ≤ Fam.card) :
    bprob q univ (fun W =>
      (ccount Fam (freeV u v a b) W : ℝ) <
        (1 - η) * (α * (Fintype.card V : ℝ) ^ (i - 4)) * q ^ (i - 4)) ≤
      Real.exp (-(η ^ 2 * (α * (Fintype.card V : ℝ) ^ (i - 4)) ^ 2 *
        q ^ (2 * (i - 4)) / (4 * ((2 : ℝ) ^ (i.choose 2) *
          (Fintype.card V : ℝ) ^ (i - 5)) * ((i - 4 : ℕ) : ℝ) * Fam.card))) := by
  have hr : 0 < i - 4 := by omega
  have hΔ : 0 < (2 : ℝ) ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - 5) := by
    have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    positivity
  have hL : 0 < α * (Fintype.card V : ℝ) ^ (i - 4) := by
    have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    positivity
  have hdeg : ∀ x : V,
      ((Fam.filter fun J => x ∈ freeV u v a b J).card : ℝ) ≤
        (2 : ℝ) ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - 5) := by
    intro x
    have hcard := card_le_card (filter_subset_filter
      (p := fun J => x ∈ freeV u v a b J) hFam)
    have hcardR : ((Fam.filter fun J => x ∈ freeV u v a b J).card : ℝ) ≤
        ((hinges G lab F u v a b i).filter
          (fun J => x ∈ freeV u v a b J)).card := by exact_mod_cast hcard
    exact hcardR.trans (hinge_free_deg hd i x)
  exact count_tail_relative q η Fam (freeV u v a b) hr
    (fun J hJ => (card_freeV hd (hFam hJ)).le)
    hΔ hdeg hL hcount hq hq1 hη hη1

theorem hinge_subfamily_tail_linear {V I : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {α q η : ℝ} {u v a b : V} {i : ℕ}
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b)
    (hi6 : 6 ≤ i) (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 0 < Fintype.card V)
    (Fam : Finset (Finset (Sym2 V)))
    (hFam : Fam ⊆ hinges G lab F u v a b i)
    (hcount : α * (Fintype.card V : ℝ) ^ (i - 4) ≤ Fam.card) :
    bprob q univ (fun W =>
      (ccount Fam (freeV u v a b) W : ℝ) <
        (1 - η) * (α * (Fintype.card V : ℝ) ^ (i - 4)) * q ^ (i - 4)) ≤
      Real.exp (-(η ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) * (Fintype.card V : ℝ) /
        (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)))) := by
  let N : ℝ := Fintype.card V
  let C : ℝ := (2 : ℝ) ^ (i.choose 2)
  let T : ℝ := N ^ (i - 5)
  let R : ℝ := (i - 4 : ℕ)
  let Q : ℝ := q ^ (2 * (i - 4))
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hC : 0 < C := by dsimp [C]; positivity
  have hT : 0 < T := pow_pos hN _
  have hR : 0 < R := by dsimp [R]; exact_mod_cast (show 0 < i - 4 by omega)
  have hp : N ^ (i - 4) = T * N := by
    dsimp [T]
    rw [← pow_succ]
    congr 1
    omega
  have hI : (Fam.card : ℝ) ≤ C * T * N := by
    obtain ⟨huv, hua, hva, hub, hvb, hab⟩ := hd
    have hu := S10V23.card_hinges_forced huv hua hva hub hvb hab i
      (∅ : Finset V) (by simp) Fam hFam (by simp)
    simpa only [card_empty, add_zero, C, N, hp, mul_assoc] using hu
  have hIpos : (0 : ℝ) < Fam.card := by
    have hL : 0 < α * N ^ (i - 4) := by positivity
    exact lt_of_lt_of_le hL (by simpa only [N] using hcount)
  have hfrac :
      η ^ 2 * (α * (T * N)) ^ 2 * Q / (4 * (C * T) * R * (C * T * N)) ≤
        η ^ 2 * (α * (T * N)) ^ 2 * Q / (4 * (C * T) * R * Fam.card) := by
    gcongr
  have heq : η ^ 2 * (α * (T * N)) ^ 2 * Q /
      (4 * (C * T) * R * (C * T * N)) =
        η ^ 2 * α ^ 2 * Q * N / (4 * C ^ 2 * R) := by
    field_simp
  calc
    _ ≤ Real.exp (-(η ^ 2 * (α * N ^ (i - 4)) ^ 2 * Q /
        (4 * (C * T) * R * Fam.card))) := by
      simpa only [N, C, T, R, Q] using
        (hinge_subfamily_tail_relative hd hi6 hα hq hq1 hη hη1 hn Fam hFam hcount)
    _ ≤ Real.exp (-(η ^ 2 * (α * (T * N)) ^ 2 * Q /
        (4 * (C * T) * R * (C * T * N)))) := by
      rw [hp]
      exact Real.exp_le_exp.mpr (neg_le_neg hfrac)
    _ = _ := by rw [heq]

#print axioms hinge_subfamily_tail_relative
#print axioms hinge_subfamily_tail_linear

end TypedTriangle.RawReference
