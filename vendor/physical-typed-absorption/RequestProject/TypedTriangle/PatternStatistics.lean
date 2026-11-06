module
public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset
noncomputable section
open Classical
set_option autoImplicit false
namespace TypedTriangle.PatternStatistics

def statistic {A : Type*} (w : Finset A → ℝ) (l : ℕ) (D : Finset A) : ℝ :=
  ∑ S ∈ D.powersetCard l, w S

def influence {A : Type*} (w : Finset A → ℝ) (l : ℕ) (D : Finset A) (a : A) : ℝ :=
  ∑ S ∈ (D.powersetCard l).filter (fun S => a ∈ S), |w S|

theorem exclusive_weight_le_influences {A : Type*} (w : Finset A → ℝ)
    (l : ℕ) (D E : Finset A) :
    (∑ S ∈ D.powersetCard l \ E.powersetCard l, |w S|) ≤
      ∑ a ∈ D \ E, influence w l D a := by
  unfold influence
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  let f := fun S : Finset A => ∑ a ∈ D \ E, if a ∈ S then |w S| else 0
  have hCover : ∀ S ∈ D.powersetCard l \ E.powersetCard l, |w S| ≤ f S := by
    intro S hS
    obtain ⟨hSD,hSE⟩ := mem_sdiff.mp hS
    obtain ⟨hSub,hCard⟩ := mem_powersetCard.mp hSD
    have hNot : ¬S ⊆ E := fun h => hSE (mem_powersetCard.mpr ⟨h,hCard⟩)
    obtain ⟨a,haS,haE⟩ := Finset.not_subset.mp hNot
    have ha : a ∈ D \ E := mem_sdiff.mpr ⟨hSub haS,haE⟩
    have hSingle := Finset.single_le_sum
      (f := fun a => if a ∈ S then |w S| else 0)
      (fun a _ => by split_ifs <;> positivity) ha
    simpa only [if_pos haS] using hSingle
  calc
    _ ≤ ∑ S ∈ D.powersetCard l \ E.powersetCard l, f S := sum_le_sum hCover
    _ ≤ ∑ S ∈ D.powersetCard l, f S := sum_le_sum_of_subset_of_nonneg sdiff_subset
      (by intro S _ _; exact sum_nonneg (fun _ _ => by split_ifs <;> positivity))

theorem statistic_difference_le_influences {A : Type*} (w : Finset A → ℝ)
    (l : ℕ) (D E : Finset A) :
    |statistic w l D - statistic w l E| ≤
      (∑ a ∈ D \ E, influence w l D a) +
      ∑ a ∈ E \ D, influence w l E a := by
  have hDifference : statistic w l D - statistic w l E =
      (∑ S ∈ D.powersetCard l \ E.powersetCard l, w S) -
      ∑ S ∈ E.powersetCard l \ D.powersetCard l, w S :=
    (Finset.sum_sdiff_sub_sum_sdiff (s₁ := E.powersetCard l)
      (s₂ := D.powersetCard l) (f := w)).symm
  rw [hDifference]
  calc
    _ ≤ |∑ S ∈ D.powersetCard l \ E.powersetCard l, w S| +
        |∑ S ∈ E.powersetCard l \ D.powersetCard l, w S| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le
        (∑ S ∈ D.powersetCard l \ E.powersetCard l, w S) 0
        (∑ S ∈ E.powersetCard l \ D.powersetCard l, w S)
    _ ≤ (∑ S ∈ D.powersetCard l \ E.powersetCard l, |w S|) +
        ∑ S ∈ E.powersetCard l \ D.powersetCard l, |w S| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := add_le_add (exclusive_weight_le_influences w l D E)
      (exclusive_weight_le_influences w l E D)

theorem nonnegative_statistic_difference_le_max {A : Type*} (w : Finset A → ℝ)
    (l : ℕ) (D E : Finset A) (hw : ∀ S, 0 ≤ w S) :
    |statistic w l D - statistic w l E| ≤
      max (∑ a ∈ D \ E, influence w l D a)
          (∑ a ∈ E \ D, influence w l E a) := by
  have hDifference : statistic w l D - statistic w l E =
      (∑ S ∈ D.powersetCard l \ E.powersetCard l, w S) -
      ∑ S ∈ E.powersetCard l \ D.powersetCard l, w S :=
    (Finset.sum_sdiff_sub_sum_sdiff (s₁ := E.powersetCard l)
      (s₂ := D.powersetCard l) (f := w)).symm
  have hD := exclusive_weight_le_influences w l D E
  have hE := exclusive_weight_le_influences w l E D
  simp only [abs_of_nonneg (hw _)] at hD hE
  have hD0 : 0 ≤ ∑ S ∈ D.powersetCard l \ E.powersetCard l, w S :=
    sum_nonneg (fun S _ => hw S)
  have hE0 : 0 ≤ ∑ S ∈ E.powersetCard l \ D.powersetCard l, w S :=
    sum_nonneg (fun S _ => hw S)
  rw [hDifference]
  apply abs_le.mpr
  constructor
  · have hMax := le_max_right (∑ a ∈ D \ E, influence w l D a)
      (∑ a ∈ E \ D, influence w l E a)
    linarith only [hD0,hE,hMax]
  · have hMax := le_max_left (∑ a ∈ D \ E, influence w l D a)
      (∑ a ∈ E \ D, influence w l E a)
    linarith only [hE0,hD,hMax]

#print axioms statistic_difference_le_influences
#print axioms nonnegative_statistic_difference_le_max
end TypedTriangle.PatternStatistics
