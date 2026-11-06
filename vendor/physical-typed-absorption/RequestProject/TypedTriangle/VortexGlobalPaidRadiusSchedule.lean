/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexExactPaidSmoothParameters
public import RequestProject.TypedTriangle.VortexGlobalRadiusSchedule
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex

/-- A fixed external extraction index bound controls every prefix of the
radius schedule. The physical inverse and its hole cap are chosen first;
an arbitrary positive profile precision may then depend on those choices.
The schedule pays that precision without changing the physical inverse. -/
theorem exists_global_paid_radius_schedule
    (α C b cap ηGlobal : ℝ) (h L : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h) (hC : 1 ≤ C)
    (hb : 0 < b) (hcap : 0 < cap) (hηGlobal : 0 < ηGlobal) :
    ∃ nGeometry : ℕ, ∃ K ηMax : ℝ → ℝ,
      ∃ Nbase Ns nPaid : ℝ → ℕ,
        (∀ x, 0 < x → 0 < K x ∧ 0 < ηMax x ∧
          1 ≤ K x * ηMax x ∧ PaidReferenceCap α h (ηMax x) nGeometry ∧
          PaidSmoothAt α x (K x) (ηMax x) h (Nbase x) (Ns x) (nPaid x)) ∧
        ∀ δProfile : ℝ → ℝ, (∀ x, 0 < x → 0 < δProfile x) →
        ∃ β : ℕ → ℝ,
          (∀ j, 0 ≤ β j) ∧
          (∀ j ≤ L, 0 < β j ∧ β j ≤ cap) ∧
          (∀ j < L, β j ≤ β (j + 1) / 2) ∧
          (∀ j k, j < k → k ≤ L →
            β j ≤ min (1 / (2 * C * K (β k))) (δProfile (β k)) /
              (16 * b * (L + 1))) ∧
          (∀ r ≤ L,
            K (β r) * (2 * b * (∑ j ∈ range r, β j)) ≤ 1 / (16 * C) ∧
            2 * b * (∑ j ∈ range r, β j) ≤ δProfile (β r) / 8) ∧
          (∑ j ∈ range (L + 1), β j) ≤ ηGlobal / 2 ∧
          ∃ N : ℕ, nGeometry ≤ N ∧
            (∀ j : Fin (L + 1),
              max (max (Nbase (β j)) (Ns (β j))) (nPaid (β j)) ≤ N) := by
  have hCpos : 0 < C := by linarith
  obtain ⟨nGeometry, K, hK, hPaid⟩ :=
    exists_exact_paid_smooth_constant_function α h hα hh
  have hChoice : ∀ x : ℝ, ∃ η : ℝ, 0 < η ∧ ∃ Nb Nj Np : ℕ,
      0 < x → 1 ≤ K x * η ∧ PaidReferenceCap α h η nGeometry ∧
        PaidSmoothAt α x (K x) η h Nb Nj Np := by
    intro x
    by_cases hx : 0 < x
    · obtain ⟨η, hη, hDom, hCap, Nb, Nj, Np, hSpec⟩ := hPaid x hx
      exact ⟨η, hη, Nb, Nj, Np, fun _ => ⟨hDom, hCap, hSpec⟩⟩
    · exact ⟨1, by norm_num, 0, 0, 0, fun hp => False.elim (hx hp)⟩
  choose ηMax hηMax Nbase Ns nPaid hSpec using hChoice
  refine ⟨nGeometry, K, ηMax, Nbase, Ns, nPaid, ?_, ?_⟩
  · intro x hx
    exact ⟨hK x hx, hηMax x, (hSpec x hx).1, (hSpec x hx).2.1, (hSpec x hx).2.2⟩
  intro δProfile hδProfile
  let εprep : ℝ → ℝ := fun x => min (1 / (2 * C * K x)) (δProfile x)
  have hεprep : ∀ x, 0 < x → 0 < εprep x := by
    intro x hx
    have hKpos : 0 < K x := hK x hx
    exact lt_min (by positivity) (hδProfile x hx)
  obtain ⟨β₀, hβ₀, hstep₀, hcross₀, hprior₀, hsum₀⟩ :=
    exists_capped_global_radius_schedule εprep b L cap ηGlobal hb hcap hηGlobal hεprep
  let β : ℕ → ℝ := fun j => β₀ (min j L)
  have hβEq : ∀ j, j ≤ L → β j = β₀ j := by
    intro j hj
    simp only [β, Nat.min_eq_left hj]
  have hβPos : ∀ j, 0 < β j := by
    intro j
    exact (hβ₀ (min j L) (Nat.min_le_right _ _)).1
  have hsumEq : ∀ r, r ≤ L + 1 →
      (∑ j ∈ range r, β j) = ∑ j ∈ range r, β₀ j := by
    intro r hr
    apply sum_congr rfl
    intro j hj
    exact hβEq j (by have := mem_range.mp hj; omega)
  have hβCap : ∀ j ≤ L, 0 < β j ∧ β j ≤ cap := by
    intro j hj
    rw [hβEq j hj]
    exact hβ₀ j hj
  have hStep : ∀ j < L, β j ≤ β (j + 1) / 2 := by
    intro j hj
    rw [hβEq j (by omega), hβEq (j + 1) (by omega)]
    exact hstep₀ j hj
  have hCross : ∀ j k, j < k → k ≤ L →
      β j ≤ min (1 / (2 * C * K (β k))) (δProfile (β k)) /
        (16 * b * (L + 1)) := by
    intro j k hjk hk
    rw [hβEq j (by omega), hβEq k hk]
    exact hcross₀ j k hjk hk
  have hPrior : ∀ r ≤ L,
      K (β r) * (2 * b * (∑ j ∈ range r, β j)) ≤ 1 / (16 * C) ∧
      2 * b * (∑ j ∈ range r, β j) ≤ δProfile (β r) / 8 := by
    intro r hr
    have hp : 2 * b * (∑ j ∈ range r, β j) ≤ εprep (β r) / 8 := by
      rw [hsumEq r (by omega), hβEq r hr]
      exact hprior₀ r hr
    have hKPos : 0 < K (β r) := hK _ (hβPos r)
    constructor
    · calc
        K (β r) * (2 * b * (∑ j ∈ range r, β j)) ≤
            K (β r) * ((1 / (2 * C * K (β r))) / 8) :=
          mul_le_mul_of_nonneg_left
            (hp.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))) hKPos.le
        _ = 1 / (16 * C) := by field_simp; ring
    · exact hp.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  let N : ℕ := max nGeometry ((univ : Finset (Fin (L + 1))).sup
    (fun j => max (max (Nbase (β j)) (Ns (β j))) (nPaid (β j))))
  refine ⟨β, (fun j => (hβPos j).le), hβCap, hStep, hCross, hPrior, ?_,
    N, le_max_left _ _, ?_⟩
  · rw [hsumEq (L + 1) le_rfl]
    exact hsum₀
  · intro j
    exact (Finset.le_sup (f := fun i : Fin (L + 1) =>
      max (max (Nbase (β i)) (Ns (β i))) (nPaid (β i))) (mem_univ j)).trans
        (le_max_right _ _)

#print axioms exists_global_paid_radius_schedule
end TypedTriangle.Vortex
