/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.RawProfileSampling
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Deterministic cost of deleting a small exceptional set from a sampled
completion profile. This does not construct the adaptive sample. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.RawReference
open S07V48

variable {V I : Type*} [Fintype V]

theorem sampled_completion_loss_bound (H : Host V I) (F : Set (Multiset I))
    (μ : Finset V → ℝ) (W A : Finset V) (u v : V) (b : ℝ)
    (hb : 0 ≤ b) (hn : 0 < (Fintype.card V : ℝ))
    (hμ : ∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b / Fintype.card V) :
    0 ≤ sampW H.G H.lab F μ W u v - sampW H.G H.lab F μ (W \ A) u v ∧
    sampW H.G H.lab F μ W u v - sampW H.G H.lab F μ (W \ A) u v ≤
      A.card * (b / Fintype.card V) := by
  let c : V → ℝ := compW H.G H.lab F μ u v
  have hc0 (a : V) : 0 ≤ c a := by
    dsimp [c, compW]
    split_ifs with h
    · exact (hμ _ h).1
    · exact le_refl _
  have hcB (a : V) : c a ≤ b / Fintype.card V := by
    dsimp [c, compW]
    split_ifs with h
    · exact (hμ _ h).2
    · exact div_nonneg hb hn.le
  have hdisj : Disjoint (W \ A) (W ∩ A) := by
    apply disjoint_left.mpr
    intro a ha hwa
    exact (mem_sdiff.mp ha).2 (mem_inter.mp hwa).2
  have hcover : (W \ A) ∪ (W ∩ A) = W := by
    ext a
    simp only [mem_union, mem_sdiff, mem_inter]
    tauto
  have heq : sampW H.G H.lab F μ W u v -
      sampW H.G H.lab F μ (W \ A) u v = ∑ a ∈ W ∩ A, c a := by
    have hsum := sum_union hdisj (f := c)
    rw [hcover] at hsum
    simpa only [sampW, wsum, c] using (sub_eq_iff_eq_add.mpr (by linarith [hsum]))
  rw [heq]
  constructor
  · exact sum_nonneg fun a _ => hc0 a
  · calc
      (∑ a ∈ W ∩ A, c a) ≤ ∑ _a ∈ W ∩ A, b / Fintype.card V :=
        sum_le_sum fun a _ => hcB a
      _ = (W ∩ A).card * (b / Fintype.card V) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ A.card * (b / Fintype.card V) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card inter_subset_right)
          (div_nonneg hb hn.le)

/-- A sampled approximate load remains approximate after an exceptional
vertex deletion, provided the removed completion mass fits the tolerance. -/
theorem sampled_profile_after_vertex_deletion (H : Host V I)
    (F : Set (Multiset I)) (μ : Finset V → ℝ) (W A : Finset V)
    (u v : V) (b q e δ : ℝ) (hb : 0 ≤ b) (hq : 0 < q)
    (hn : 0 < (Fintype.card V : ℝ))
    (hμ : ∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b / Fintype.card V)
    (hraw : |sampW H.G H.lab F μ W u v / q - 1| ≤ e)
    (hbudget : A.card * (b / Fintype.card V) ≤ q * δ) :
    |sampW H.G H.lab F μ (W \ A) u v / q - 1| ≤ e + δ := by
  obtain ⟨hl0, hl⟩ := sampled_completion_loss_bound H F μ W A u v b hb hn hμ
  have hlq : 0 ≤ (sampW H.G H.lab F μ W u v -
        sampW H.G H.lab F μ (W \ A) u v) / q ∧
      (sampW H.G H.lab F μ W u v -
        sampW H.G H.lab F μ (W \ A) u v) / q ≤ δ :=
    ⟨div_nonneg hl0 hq.le,
      (div_le_iff₀ hq).mpr (hl.trans (by simpa [mul_comm] using hbudget))⟩
  have heq : sampW H.G H.lab F μ (W \ A) u v / q - 1 =
      (sampW H.G H.lab F μ W u v / q - 1) -
        (sampW H.G H.lab F μ W u v -
          sampW H.G H.lab F μ (W \ A) u v) / q := by ring
  rw [heq]
  rw [abs_le] at hraw ⊢
  constructor <;> linarith [hraw.1, hraw.2, hlq.1, hlq.2]

#print axioms sampled_completion_loss_bound
#print axioms sampled_profile_after_vertex_deletion

end TypedTriangle.RawReference
