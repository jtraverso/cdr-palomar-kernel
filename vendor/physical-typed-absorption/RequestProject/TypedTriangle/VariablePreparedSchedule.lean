/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VariablePreparedCore
public import RequestProject.TypedTriangle.VariablePreparedProfile
public import RequestProject.TypedTriangle.VortexGlobalRadiusSchedule
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Compose the variable first-entry core with a finite radius schedule.
The deletion before the first successful index pays only earlier radii. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem scheduled_prepared_core (α τ C q : ℝ) (h : ℕ) (K : ℝ → ℝ)
    (hα : 0 < α) (hτ : 0 < τ) (hC : 1 ≤ C) (hq : 0 < q)
    (hK : ∀ x, 0 < x → 0 < K x) :
    ∃ (L : ℕ) (β : ℕ → ℝ) (ξ : ℝ), 0 < ξ ∧
      (∀ j ≤ L, 0 < β j) ∧
      (∀ j k, j < k → k ≤ L →
        β j ≤ prepTolerance (K (β k)) C q / (16 * C * (L + 1))) ∧
      ∀ N : ℕ, ∃ n₀ : ℕ,
        ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
          n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
          ∃ r ≤ L, ∃ A : Finset V,
            A.card ≤ TypedTriangle.priorBudget
              (fun j => ⌊β j * Fintype.card V⌋₊) r ∧
            (A.card : ℝ) ≤ τ * Fintype.card V ∧
            CommonNbrCond (restrictedHost H A) F (α / 2) ∧
            HingeCond (restrictedHost H A) F (α / 2) h ∧
            Dispersal.PreparedCore (restrictedHost H A).G
              (restrictedHost H A).lab F (α / 4) h N (β r) ∧
            K (β r) * (ξ + (A.card : ℝ) * C /
              (q * Fintype.card V)) ≤ 1 / (4 * C) := by
  obtain ⟨η, δ₁, hη, hδ₁, L, hcore⟩ :=
    TypedTriangle.preparedCore_at_variable_radius α τ h hα hτ
  have hCpos : 0 < C := by linarith
  let cap : ℝ := min (1 / 4) δ₁
  have hcap : 0 < cap := lt_min (by norm_num) hδ₁
  have hprep : ∀ x, 0 < x → 0 < prepTolerance (K x) C q := by
    intro x hx
    exact prepTolerance_pos (hK x hx) hCpos hq
  obtain ⟨β, hβ, -, hcross, hbudget, hsum⟩ :=
    exists_capped_global_radius_schedule
      (fun x => prepTolerance (K x) C q) C L cap η hCpos hcap hη hprep
  have hKβ : ∀ j ≤ L, 0 < K (β j) := by
    intro j hj
    exact hK _ (hβ j hj).1
  obtain ⟨ξ, hξ, hξbudget⟩ :=
    exists_uniform_exactification_window β K L (1 / (2 * C)) C
      (by positivity) hCpos hKβ
  refine ⟨L, β, ξ, hξ, (fun j hj => (hβ j hj).1), hcross, ?_⟩
  intro N
  obtain ⟨n₀, hmain⟩ := hcore N
  refine ⟨max n₀ 1, ?_⟩
  intro V I _ H F hn hH3 hH4
  obtain ⟨r, hr, A, hA, hAτ, hA3, hA4, hPc⟩ :=
    hmain β (fun j hj => by simpa only [cap] using hβ j hj) hsum H F
      ((le_max_left _ _).trans hn) hH3 hH4
  refine ⟨r, hr, A, hA, hAτ, hA3, hA4, hPc, ?_⟩
  have hnpos : 0 < Fintype.card V := by
    have hlarge : 1 ≤ Fintype.card V := (le_max_right _ _).trans hn
    omega
  have hfloor : (TypedTriangle.priorBudget
      (fun j => ⌊β j * Fintype.card V⌋₊) r : ℝ) ≤
      (∑ j ∈ range r, β j) * Fintype.card V := by
    simp only [TypedTriangle.priorBudget]
    rw [Nat.cast_sum]
    have hterm : ∀ j ∈ range r,
        (⌊β j * Fintype.card V⌋₊ : ℝ) ≤ β j * Fintype.card V := by
      intro j hj
      have hjr : j < r := mem_range.mp hj
      exact Nat.floor_le (mul_nonneg
        (hβ j (Nat.le_trans (Nat.le_of_lt hjr) hr)).1.le (by positivity))
    calc
      (∑ j ∈ range r, (⌊β j * Fintype.card V⌋₊ : ℝ))
          ≤ ∑ j ∈ range r, β j * Fintype.card V := sum_le_sum hterm
      _ = (∑ j ∈ range r, β j) * Fintype.card V := by rw [sum_mul]
  have hsumBudget := hbudget r hr
  have hprior : (TypedTriangle.priorBudget
      (fun j => ⌊β j * Fintype.card V⌋₊) r : ℝ) ≤
      prepTolerance (K (β r)) C q * Fintype.card V := by
    have hsumSmall : (∑ j ∈ range r, β j) ≤
        prepTolerance (K (β r)) C q := by
      have hsnonneg : (0 : ℝ) ≤ ∑ j ∈ range r, β j := by
        apply sum_nonneg
        intro j hj
        have hjr : j < r := mem_range.mp hj
        exact (hβ j (Nat.le_trans (Nat.le_of_lt hjr) hr)).1.le
      have hle : (∑ j ∈ range r, β j) ≤
          2 * C * (∑ j ∈ range r, β j) := by nlinarith
      have hpp : 0 ≤ prepTolerance (K (β r)) C q :=
        (hprep (β r) (hβ r hr).1).le
      linarith
    exact hfloor.trans (mul_le_mul_of_nonneg_right hsumSmall (by positivity))
  have hξsmall : K (β r) * ξ ≤ 1 / (8 * C) := by
    have hh := hξbudget r hr
    calc
      K (β r) * ξ ≤ K (β r) * (ξ + 4 * C * ξ) := by
        apply mul_le_mul_of_nonneg_left _ (hKβ r hr).le
        nlinarith [mul_pos hCpos hξ]
      _ ≤ 1 / (2 * C) / 4 := hh
      _ = 1 / (8 * C) := by ring
  exact variable_entry_exactification_budget (hKβ r hr) hCpos hq hnpos hA hprior hξsmall

#print axioms scheduled_prepared_core

end TypedTriangle.Vortex
