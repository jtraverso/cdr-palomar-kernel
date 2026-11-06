/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexRadiusBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A finite schedule for the *global extraction index*. The index is bounded
independently of the number of sampled levels; no radius is chosen by a
fixed-point argument involving its own preparation tolerance. -/

open Finset
noncomputable section

namespace TypedTriangle.Vortex

private theorem positive_prefix_lower (ε : ℕ → ℝ) (L : ℕ)
    (hε : ∀ k ≤ L, 0 < ε k) :
    ∃ e : ℝ, 0 < e ∧ ∀ k ≤ L, e ≤ ε k := by
  induction L with
  | zero =>
      refine ⟨ε 0, hε 0 (by omega), ?_⟩
      intro k hk
      have : k = 0 := by omega
      simp [this]
  | succ L ih =>
      obtain ⟨e, he, heBound⟩ := ih (by
        intro k hk
        exact hε k (by omega))
      refine ⟨min e (ε (L + 1)), lt_min he (hε (L + 1) (by omega)), ?_⟩
      intro k hk
      by_cases h : k ≤ L
      · exact (min_le_left _ _).trans (heBound k h)
      · have : k = L + 1 := by omega
        subst k
        exact min_le_right _ _

/-- Choose all robustness radii after knowing the finitely many preparation
tolerances and before knowing the host or the number of sampled levels. -/
theorem exists_global_radius_schedule (ε : ℕ → ℝ) (b : ℝ) (L : ℕ)
    (hb : 0 < b) (hε : ∀ k ≤ L, 0 < ε k) :
    ∃ β : ℕ → ℝ,
      (∀ j ≤ L, 0 < β j) ∧
      (∀ j < L, β j ≤ β (j + 1) / 2) ∧
      (∀ j k, j < k → k ≤ L →
        β j ≤ ε k / (16 * b * (L + 1))) ∧
      (∀ r ≤ L, 2 * b * (∑ j ∈ range r, β j) ≤ ε r / 8) := by
  obtain ⟨e, he, heBound⟩ := positive_prefix_lower ε L hε
  let ρ : ℝ := min (1 / 2) (e / (16 * b * (L + 1)))
  have hden : 0 < 16 * b * (L + 1 : ℝ) := by positivity
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos he hden)
  have hρhalf : ρ ≤ 1 / 2 := min_le_left _ _
  have hρone : ρ ≤ 1 := by linarith
  let β : ℕ → ℝ := fun j => ρ ^ (L + 1 - j)
  have hβpos : ∀ j ≤ L, 0 < β j := by
    intro j _
    exact pow_pos hρ _
  have hβstep : ∀ j < L, β j ≤ β (j + 1) / 2 := by
    intro j hj
    have hexp : L + 1 - j = (L + 1 - (j + 1)) + 1 := by omega
    dsimp [β]
    rw [hexp, pow_succ]
    have hp : 0 ≤ ρ ^ (L + 1 - (j + 1)) := (pow_pos hρ _).le
    nlinarith [mul_le_mul_of_nonneg_left hρhalf hp]
  have hβρ : ∀ j ≤ L, β j ≤ ρ := by
    intro j hj
    have hn : 1 ≤ L + 1 - j := by omega
    have hexp : L + 1 - j = (L - j) + 1 := by omega
    dsimp [β]
    rw [hexp, pow_succ]
    have hpow : ρ ^ (L - j) ≤ 1 := pow_le_one₀ hρ.le hρone
    nlinarith [mul_le_mul_of_nonneg_right hpow hρ.le]
  have hcross : ∀ j k, j < k → k ≤ L →
      β j ≤ ε k / (16 * b * (L + 1)) := by
    intro j k hjk hk
    calc
      β j ≤ ρ := hβρ j (by omega)
      _ ≤ e / (16 * b * (L + 1)) := min_le_right _ _
      _ ≤ ε k / (16 * b * (L + 1)) :=
        div_le_div_of_nonneg_right (heBound k hk) hden.le
  refine ⟨β, hβpos, hβstep, hcross, ?_⟩
  intro r hr
  exact earlier_radii_within_window β ε b hb L r hr (hε r hr).le
    (by intro j hj; exact hcross j r hj hr)

private def radiusState (εprep : ℝ → ℝ) (b : ℝ) (L : ℕ) (βTop : ℝ) :
    ℕ → ℝ × ℝ
  | 0 => (βTop, εprep βTop)
  | r + 1 =>
      let s := radiusState εprep b L βTop r
      let next := min (s.1 / 2) (s.2 / (16 * b * (L + 1))) / 2
      (next, min s.2 (εprep next))

private theorem radiusState_pos (εprep : ℝ → ℝ) (b : ℝ) (L r : ℕ)
    (βTop : ℝ) (hb : 0 < b) (hTop : 0 < βTop)
    (hε : ∀ x, 0 < x → 0 < εprep x) :
    0 < (radiusState εprep b L βTop r).1 ∧
    0 < (radiusState εprep b L βTop r).2 := by
  induction r with
  | zero => exact ⟨by simpa [radiusState] using hTop,
      by simpa [radiusState] using hε βTop hTop⟩
  | succ r ih =>
      have hden : 0 < 16 * b * (L + 1 : ℝ) := by positivity
      have hnext : 0 < min ((radiusState εprep b L βTop r).1 / 2)
          ((radiusState εprep b L βTop r).2 / (16 * b * (L + 1))) / 2 := by
        exact half_pos (lt_min (half_pos ih.1) (div_pos ih.2 hden))
      exact ⟨by simpa only [radiusState] using hnext,
        by simpa only [radiusState] using lt_min ih.2 (hε _ hnext)⟩

private theorem radiusState_min_le (εprep : ℝ → ℝ) (b : ℝ) (L r t : ℕ)
    (βTop : ℝ)
    (ht : t ≤ r) :
    (radiusState εprep b L βTop r).2 ≤
      εprep (radiusState εprep b L βTop t).1 := by
  induction r with
  | zero =>
      have : t = 0 := by omega
      subst t
      simp [radiusState]
  | succ r ih =>
      by_cases h : t ≤ r
      · have hleft : (radiusState εprep b L βTop (r + 1)).2 ≤
            (radiusState εprep b L βTop r).2 := by
          change min (radiusState εprep b L βTop r).2
            (εprep (min ((radiusState εprep b L βTop r).1 / 2)
              ((radiusState εprep b L βTop r).2 / (16 * b * (L + 1))) / 2)) ≤ _
          exact min_le_left _ _
        exact hleft.trans (ih h)
      · have : t = r + 1 := by omega
        subst t
        simp only [radiusState]
        exact min_le_right _ _

private theorem radiusState_first_le_top (εprep : ℝ → ℝ) (b : ℝ)
    (L r : ℕ) (βTop : ℝ) (hb : 0 < b) (hTop : 0 < βTop)
    (hε : ∀ x, 0 < x → 0 < εprep x) :
    (radiusState εprep b L βTop r).1 ≤ βTop := by
  induction r with
  | zero => simp [radiusState]
  | succ r ih =>
      have hprev : 0 ≤ (radiusState εprep b L βTop r).1 :=
        (radiusState_pos εprep b L r βTop hb hTop hε).1.le
      have hmin : min ((radiusState εprep b L βTop r).1 / 2)
          ((radiusState εprep b L βTop r).2 / (16*b*(L+1))) ≤
          (radiusState εprep b L βTop r).1 / 2 := min_le_left _ _
      change min ((radiusState εprep b L βTop r).1 / 2)
          ((radiusState εprep b L βTop r).2 / (16*b*(L+1))) / 2 ≤ βTop
      linarith

/-- Backward choice for the genuine dependency `εprep (β k)`. There are at
most `L` strict quotient changes, so this schedule is fixed before any
sampled chain, regardless of its depth. -/
theorem exists_dependent_global_radius_schedule (εprep : ℝ → ℝ)
    (b : ℝ) (L : ℕ) (βTop : ℝ) (hb : 0 < b) (hTop : 0 < βTop)
    (hε : ∀ x, 0 < x → 0 < εprep x) :
    ∃ β : ℕ → ℝ,
      (∀ j ≤ L, 0 < β j) ∧
      (∀ j < L, β j ≤ β (j + 1) / 2) ∧
      (∀ j k, j < k → k ≤ L →
        β j ≤ εprep (β k) / (16 * b * (L + 1))) ∧
      (∀ r ≤ L, 2 * b * (∑ j ∈ range r, β j) ≤ εprep (β r) / 8) ∧
      (∀ j ≤ L, β j ≤ βTop) ∧
      (∑ j ∈ range (L + 1), β j) ≤ (L + 1 : ℝ) * βTop := by
  let β : ℕ → ℝ := fun j => (radiusState εprep b L βTop (L - j)).1
  have hβpos : ∀ j ≤ L, 0 < β j := by
    intro j _
    exact (radiusState_pos εprep b L (L-j) βTop hb hTop hε).1
  have hβstep : ∀ j < L, β j ≤ β (j + 1) / 2 := by
    intro j hj
    have hs : L - j = (L - (j + 1)) + 1 := by omega
    have hleft : β j =
        min ((radiusState εprep b L βTop (L - (j + 1))).1 / 2)
          ((radiusState εprep b L βTop (L - (j + 1))).2 / (16*b*(L+1))) / 2 := by
      dsimp only [β]
      rw [hs]
      rfl
    rw [hleft]
    change _ ≤ (radiusState εprep b L βTop (L - (j + 1))).1 / 2
    have hm : min ((radiusState εprep b L βTop (L - (j + 1))).1 / 2)
        ((radiusState εprep b L βTop (L - (j + 1))).2 / (16*b*(L+1))) ≤
        (radiusState εprep b L βTop (L - (j + 1))).1 / 2 := min_le_left _ _
    have hprev : 0 ≤ (radiusState εprep b L βTop (L - (j + 1))).1 :=
      (radiusState_pos εprep b L _ βTop hb hTop hε).1.le
    linarith
  have hcross : ∀ j k, j < k → k ≤ L →
      β j ≤ εprep (β k) / (16 * b * (L + 1)) := by
    intro j k hjk hk
    have hr : L - j = (L - j - 1) + 1 := by omega
    have ht : L - k ≤ L - j - 1 := by omega
    have hmin := radiusState_min_le εprep b L (L-j-1) (L-k) βTop ht
    have hden : 0 < 16 * b * (L + 1 : ℝ) := by positivity
    have hcomp :
        (radiusState εprep b L βTop (L-j-1)).2 / (16*b*(L+1)) ≤
        εprep (radiusState εprep b L βTop (L-k)).1 / (16*b*(L+1)) :=
      div_le_div_of_nonneg_right hmin hden.le
    have hleft : β j =
        min ((radiusState εprep b L βTop (L-j-1)).1 / 2)
          ((radiusState εprep b L βTop (L-j-1)).2 / (16*b*(L+1))) / 2 := by
      dsimp only [β]
      rw [hr]
      rfl
    rw [hleft]
    change _ ≤ εprep (radiusState εprep b L βTop (L-k)).1 / (16*b*(L+1))
    have hm : min ((radiusState εprep b L βTop (L-j-1)).1 / 2)
        ((radiusState εprep b L βTop (L-j-1)).2 / (16*b*(L+1))) ≤
        (radiusState εprep b L βTop (L-j-1)).2 / (16*b*(L+1)) := min_le_right _ _
    have hnum : 0 ≤ (radiusState εprep b L βTop (L-j-1)).2 :=
      (radiusState_pos εprep b L _ βTop hb hTop hε).2.le
    have hfrac : 0 ≤ (radiusState εprep b L βTop (L-j-1)).2 /
        (16*b*(L+1)) := div_nonneg hnum hden.le
    linarith
  have hβtop : ∀ j ≤ L, β j ≤ βTop := by
    intro j _
    exact radiusState_first_le_top εprep b L (L-j) βTop hb hTop hε
  refine ⟨β, hβpos, hβstep, hcross, ?_, hβtop, ?_⟩
  · intro r hr
    exact earlier_radii_within_window β (fun j => εprep (β j)) b hb L r hr
      (hε _ (hβpos r hr)).le
      (by intro j hj; exact hcross j r hj hr)
  · calc
      (∑ j ∈ range (L + 1), β j) ≤ ∑ _j ∈ range (L + 1), βTop := by
        apply Finset.sum_le_sum
        intro j hj
        exact hβtop j (by simpa using hj)
      _ = (L + 1 : ℝ) * βTop := by simp [nsmul_eq_mul]

/-- The global schedule also fits a prescribed cap and a prescribed total
activation budget, with no dependence on the number of sampled layers. -/
theorem exists_capped_global_radius_schedule (εprep : ℝ → ℝ)
    (b : ℝ) (L : ℕ) (cap η : ℝ) (hb : 0 < b)
    (hcap : 0 < cap) (hη : 0 < η)
    (hε : ∀ x, 0 < x → 0 < εprep x) :
    ∃ β : ℕ → ℝ,
      (∀ j ≤ L, 0 < β j ∧ β j ≤ cap) ∧
      (∀ j < L, β j ≤ β (j + 1) / 2) ∧
      (∀ j k, j < k → k ≤ L →
        β j ≤ εprep (β k) / (16 * b * (L + 1))) ∧
      (∀ r ≤ L, 2 * b * (∑ j ∈ range r, β j) ≤ εprep (β r) / 8) ∧
      (∑ j ∈ range (L + 1), β j) ≤ η / 2 := by
  let βTop : ℝ := min cap (η / (2 * (L + 1 : ℝ)))
  have hTop : 0 < βTop := lt_min hcap (by positivity)
  obtain ⟨β, hpos, hstep, hcross, hbudget, htop, hsum⟩ :=
    exists_dependent_global_radius_schedule εprep b L βTop hb hTop hε
  refine ⟨β, ?_, hstep, hcross, hbudget, ?_⟩
  · intro j hj
    exact ⟨hpos j hj, (htop j hj).trans (min_le_left _ _)⟩
  · have htopη : βTop ≤ η / (2 * (L + 1 : ℝ)) := min_le_right _ _
    have hfactor : 0 ≤ (L + 1 : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left htopη hfactor
    have heq : (L + 1 : ℝ) * (η / (2 * (L + 1 : ℝ))) = η / 2 := by
      field_simp
    linarith

/-- Once the finite radius list has been chosen, one common error window pays
all its smooth-inverse bounds. In particular, this choice follows the radius
list and creates no self-dependence in the preparation tolerances. -/
theorem exists_uniform_exactification_window (β : ℕ → ℝ) (K : ℝ → ℝ)
    (L : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hK : ∀ j ≤ L, 0 < K (β j)) :
    ∃ ξ : ℝ, 0 < ξ ∧
      ∀ j ≤ L, K (β j) * (ξ + 4 * b * ξ) ≤ a / 4 := by
  let M : ℝ := (∑ j ∈ range (L + 1), K (β j)) + 1
  have hM : 0 < M := by
    have hsum : 0 ≤ ∑ j ∈ range (L + 1), K (β j) := by
      apply Finset.sum_nonneg
      intro j hj
      exact (hK j (by simpa using hj)).le
    dsimp [M]
    linarith
  have hMbound : ∀ j ≤ L, K (β j) ≤ M := by
    intro j hj
    have hsingle : K (β j) ≤ ∑ k ∈ range (L + 1), K (β k) := by
      apply Finset.single_le_sum (s := range (L + 1)) (f := fun k => K (β k))
      · intro k hk
        exact (hK k (by simpa using hk)).le
      · simp [mem_range, hj]
    dsimp [M]
    linarith
  let ξ : ℝ := a / (8 * M * (1 + 4 * b))
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  refine ⟨ξ, hξ, ?_⟩
  intro j hj
  have hfactor : 0 ≤ ξ + 4 * b * ξ := by positivity
  have hbound := mul_le_mul_of_nonneg_right (hMbound j hj) hfactor
  have hEq : M * (ξ + 4 * b * ξ) = a / 8 := by
    dsimp [ξ]
    field_simp
  linarith

/-- A layer error that doubles toward the terminal scale has a total cost
bounded by twice its terminal cost, even when the number of layers depends
on the host order. This is a numerical interface: constructing such errors
from the simultaneous sampling tests is a separate obligation. -/
theorem finite_depth_geometric_error_budget (e : ℕ → ℝ) (m : ℕ)
    (he : ∀ j ≤ m, 0 ≤ e j)
    (hstep : ∀ j < m, e j ≤ e (j + 1) / 2) :
    ∑ j ∈ range (m + 1), e j ≤ 2 * e m := by
  induction m with
  | zero => simp; linarith [he 0 (by omega)]
  | succ m ih =>
      have he' : ∀ j ≤ m, 0 ≤ e j := by
        intro j hj
        exact he j (by omega)
      have hstep' : ∀ j < m, e j ≤ e (j + 1) / 2 := by
        intro j hj
        exact hstep j (by omega)
      rw [Finset.sum_range_succ]
      linarith [ih he' hstep', hstep m (by omega)]

#print axioms exists_global_radius_schedule
#print axioms exists_dependent_global_radius_schedule
#print axioms exists_capped_global_radius_schedule
#print axioms exists_uniform_exactification_window
#print axioms finite_depth_geometric_error_budget

end TypedTriangle.Vortex
