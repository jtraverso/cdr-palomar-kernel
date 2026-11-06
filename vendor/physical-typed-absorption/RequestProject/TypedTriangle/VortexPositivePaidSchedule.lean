/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexScheduledPaidSmoothCore
public import RequestProject.TypedTriangle.VortexScheduledSampleBudgetBridge
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex

/-! The smooth inverse is selected before the finite radius schedule. Only
after all candidate radii are known does the caller supply the finitely many
reference tolerances. A single raw sampling precision serves all candidates.
The schedule is run with coefficient cap `2*C`, leaving one half of the H1
budget for the paid holes. -/

theorem positive_paid_schedule_before_sample (α τ C q : ℝ) (h : ℕ)
    (hα : 0 < α) (hτ : 0 < τ) (hC : 1 ≤ C) (hq : 0 < q)
    (hh : 6 ≤ h) :
    ∃ (K : ℝ → ℝ) (L : ℕ) (β : ℕ → ℝ) (ξSchedule : ℝ),
      ∃ (η : Fin (L + 1) → ℝ)
        (Nbase Ns nPaid : Fin (L + 1) → ℕ) (N n₀ : ℕ),
        0 < ξSchedule ∧
        (∀ j ≤ L, 0 < β j ∧ 0 < K (β j)) ∧
        (∀ j k, j < k → k ≤ L →
          β j ≤ prepTolerance (K (β k)) (2 * C) q /
            (16 * (2 * C) * (L + 1))) ∧
        (∀ j : Fin (L + 1), 0 < η j ∧
          PaidSmoothAt (α / 4) (β j) (K (β j)) (η j) h
            (Nbase j) (Ns j) (nPaid j)) ∧
        (∀ j : Fin (L + 1),
          max (max (Nbase j) (Ns j)) (nPaid j) ≤ N) ∧
        ∀ (εRef : Fin (L + 1) → ℝ),
          (∀ j, 0 < εRef j) →
          ∃ ξSample : ℝ, 0 < ξSample ∧ ξSample ≤ ξSchedule ∧
            (∀ j, ξSample ≤ εRef j / 2) ∧
            ∀ {V I : Type} [Fintype V] (H : Host V I)
              (F : Set (Multiset I)),
              n₀ ≤ Fintype.card V →
              CommonNbrCond H F α → HingeCond H F α h →
              ∃ r ≤ L, ∃ A : Finset V,
                A.card ≤ TypedTriangle.priorBudget
                  (fun j => ⌊β j * Fintype.card V⌋₊) r ∧
                (A.card : ℝ) ≤ τ * Fintype.card V ∧
                CommonNbrCond (restrictedHost H A) F (α / 2) ∧
                HingeCond (restrictedHost H A) F (α / 2) h ∧
                Dispersal.PreparedCore (restrictedHost H A).G
                  (restrictedHost H A).lab F (α / 4) h N (β r) ∧
                K (β r) * (ξSample + (A.card : ℝ) * C /
                  (q * Fintype.card V)) ≤ 1 / (8 * C) := by
  have hTwoC : 1 ≤ 2 * C := by linarith
  have hα4 : 0 < α / 4 := by positivity
  obtain ⟨K, hKpos, hPaid⟩ :=
    exists_paid_smooth_constant_function (α / 4) h hα4 hh
  obtain ⟨L, β, ξSchedule, hξSchedule, hβ, hCross, hPrepared⟩ :=
    scheduled_prepared_core α τ (2 * C) q h K
      hα hτ hTwoC hq hKpos
  have hChoice : ∀ j : Fin (L + 1),
      ∃ ηj : ℝ, 0 < ηj ∧ ∃ Nb Nj Np : ℕ,
        PaidSmoothAt (α / 4) (β j) (K (β j)) ηj h Nb Nj Np := by
    intro j
    obtain ⟨ηj, hηj, Nb, Nj, Np, hspec⟩ :=
      hPaid (β j) (hβ j (Nat.le_of_lt_succ j.isLt))
    exact ⟨ηj, hηj, Nb, Nj, Np, hspec⟩
  choose η hη Nbase Ns nPaid hSpec using hChoice
  let N : ℕ := (univ : Finset (Fin (L + 1))).sup
    (fun j => max (max (Nbase j) (Ns j)) (nPaid j))
  obtain ⟨nPrepared, hPreparedN⟩ := hPrepared N
  let n₀ := max nPrepared 1
  refine ⟨K, L, β, ξSchedule, η, Nbase, Ns, nPaid, N, n₀,
    hξSchedule, (fun j hj => ⟨hβ j hj, hKpos _ (hβ j hj)⟩),
    hCross, (fun j => ⟨hη j, hSpec j⟩),
    (fun j => Finset.le_sup (f := fun i : Fin (L + 1) =>
      max (max (Nbase i) (Ns i)) (nPaid i)) (Finset.mem_univ j)), ?_⟩
  intro εRef hRef
  obtain ⟨ξSample, hξSample, hξLe, hξRef⟩ :=
    exists_sample_precision_for_finite_references L ξSchedule εRef
      hξSchedule hRef
  refine ⟨ξSample, hξSample, hξLe, hξRef, ?_⟩
  intro V I _ H F hn hH3 hH4
  have hnPrepared : nPrepared ≤ Fintype.card V :=
    (le_max_left _ _).trans hn
  obtain ⟨r, hr, A, hA, hAτ, hA3, hA4, hCore, hBudget⟩ :=
    hPreparedN H F hnPrepared hH3 hH4
  have hnPos : (0 : ℝ) < Fintype.card V := by
    have hOne : 1 ≤ Fintype.card V := (le_max_right _ _).trans hn
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hOne
  have hBudget' : K (β r) *
      (ξSample + (A.card : ℝ) * C / (q * Fintype.card V)) ≤
      1 / (8 * C) := by
    have hOld : K (β r) *
        (ξSchedule + (A.card : ℝ) * (2 * C) /
          (q * Fintype.card V)) ≤ 1 / (8 * C) := by
      convert hBudget using 1 <;> ring
    exact scheduled_sample_budget_transfers_to_ambient C q (K (β r))
      ξSample ξSchedule (Fintype.card V) (Fintype.card V) A.card
      hC hq (hKpos _ (hβ r hr)).le hnPos le_rfl hξLe hOld
  exact ⟨r, hr, A, hA, hAτ, hA3, hA4, hCore, hBudget'⟩

#print axioms positive_paid_schedule_before_sample

end TypedTriangle.Vortex
