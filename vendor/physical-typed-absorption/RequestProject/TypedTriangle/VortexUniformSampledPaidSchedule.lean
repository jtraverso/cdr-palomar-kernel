/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexUniformRouteBeforePrecision
public import RequestProject.TypedTriangle.VortexPositivePaidSchedule
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000

namespace TypedTriangle.Vortex
open CorePaid

/-- The route and the finite paid-preparation schedule are fixed before a
weighted sample is requested. The sampled window `W` and the preparation cut
`A` are obtained from the same host; the inverse budget is on this actual
sampled core. Dense reference and bank activation are deliberately separate. -/
theorem uniform_sampled_paid_schedule_before_host {I : Type}
    (F : Set (Multiset I)) (α q C : ℝ) (h : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hC : 1 ≤ C) (hh : 6 ≤ h) :
    let αW := α * q ^ h / 2
    ∃ (t : ℕ) (ε θ τPrep : ℝ),
      Odd t ∧ 3 ≤ t ∧ 0 < ε ∧ 0 < θ ∧
      0 < τPrep ∧ τPrep ≤ ε / 2 ∧ τPrep ≤ q / 8 ∧
      ∃ (K : ℝ → ℝ) (L : ℕ) (β : ℕ → ℝ) (ξSchedule : ℝ),
        ∃ (η : Fin (L + 1) → ℝ)
          (Nbase Ns nPaid : Fin (L + 1) → ℕ) (N : ℕ),
          0 < ξSchedule ∧
          (∀ j ≤ L, 0 < β j ∧ 0 < K (β j)) ∧
          (∀ j : Fin (L + 1), 0 < η j ∧
            PaidSmoothAt (αW / 4) (β j) (K (β j)) (η j) h
              (Nbase j) (Ns j) (nPaid j)) ∧
          ∀ (εRef : Fin (L + 1) → ℝ),
            (∀ j, 0 < εRef j) →
            ∃ ξSample : ℝ, 0 < ξSample ∧ ξSample ≤ ξSchedule ∧
              (∀ j, ξSample ≤ εRef j / 2) ∧
              ∃ n₀ : ℕ,
                ∀ {V : Type} [Fintype V] (H : Host V I)
                  (φ : Finset V → ℝ),
                  n₀ ≤ Fintype.card V →
                  IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
                  CommonNbrCond H F α → HingeCond H F α h →
                  ∃ (W : Finset V)
                    (A : Finset (Survivors (univ \ W))) (r : ℕ),
                    r ≤ L ∧
                    q * Fintype.card V / 2 ≤ W.card ∧
                    (W.card : ℝ) < 2 * q * Fintype.card V ∧
                    S07V27.RouteProp H.G H.lab F t ε W ∧
                    (∀ u v, H.G.Adj u v →
                      |S07V48.sampW H.G H.lab F φ W u v / q - 1| ≤ ξSample) ∧
                    (A.card : ℝ) ≤ τPrep * W.card ∧
                    CommonNbrCond
                      (restrictedHost (restrictedHost H (univ \ W)) A) F
                      (αW / 2) ∧
                    HingeCond
                      (restrictedHost (restrictedHost H (univ \ W)) A) F
                      (αW / 2) h ∧
                    Dispersal.PreparedCore
                      (restrictedHost (restrictedHost H (univ \ W)) A).G
                      (restrictedHost (restrictedHost H (univ \ W)) A).lab
                      F (αW / 4) h N (β r) ∧
                    K (β r) * (ξSample + (A.card : ℝ) * C /
                      (q * W.card)) ≤ 1 / (8 * C) := by
  let αW := α * q ^ h / 2
  have hαW : 0 < αW := by dsimp [αW]; positivity
  obtain ⟨t, ε, θ, ht, ht3, hε, hθ, hWindow⟩ :=
    native_shared_core_preparation_route_before_precision
      α q C h hα hq hq1 hC hh
  let τPrep := min (ε / 4) (q / 8)
  have hτPrep : 0 < τPrep := by dsimp [τPrep]; positivity
  have hτRoute : τPrep ≤ ε / 2 := by
    have hc : τPrep ≤ ε / 4 := min_le_left _ _
    linarith
  have hτQ : τPrep ≤ q / 8 := min_le_right _ _
  obtain ⟨K, L, β, ξSchedule, η, Nbase, Ns, nPaid, N, nPrep,
    hξSchedule, hβK, _hCross, hPaid, _hN, hSchedule⟩ :=
    positive_paid_schedule_before_sample αW τPrep C q h
      hαW hτPrep hC hq hh
  refine ⟨t, ε, θ, τPrep, ht, ht3, hε, hθ,
    hτPrep, hτRoute, hτQ,
    K, L, β, ξSchedule, η, Nbase, Ns, nPaid, N,
    hξSchedule, hβK, hPaid, ?_⟩
  intro εRef hRef
  obtain ⟨ξSample, hξSample, hξLe, hξRef, hPrepared⟩ :=
    hSchedule εRef hRef
  obtain ⟨δ, nSample, _hδ, hSample⟩ := hWindow τPrep hτPrep ξSample hξSample
  let n₀ := max nSample ⌈2 * (nPrep : ℝ) / q⌉₊
  refine ⟨ξSample, hξSample, hξLe, hξRef, n₀, ?_⟩
  intro V _ H φ hn hSeed hPhysical hH3 hH4
  have hnSample : nSample ≤ Fintype.card V := (le_max_left _ _).trans hn
  obtain ⟨W, hWlo, hWhi, _hContract, hRoute, _hGood, _hPool,
    hRaw, h3W, h4W, _hWithdraw⟩ :=
    hSample H F φ hH3 hH4 hPhysical hSeed hnSample
  have hnCeil : ⌈2 * (nPrep : ℝ) / q⌉₊ ≤ Fintype.card V :=
    (le_max_right _ _).trans hn
  have hNPrep : nPrep ≤ Fintype.card (Survivors (univ \ W)) := by
    rw [CorePaid.card_survivors_compl]
    have hceil : (⌈2 * (nPrep : ℝ) / q⌉₊ : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hnCeil
    have htwo : 2 * (nPrep : ℝ) ≤
        (⌈2 * (nPrep : ℝ) / q⌉₊ : ℝ) * q :=
      (div_le_iff₀ hq).mp (Nat.le_ceil _)
    have hscale := mul_le_mul_of_nonneg_left hceil hq.le
    exact_mod_cast (show (nPrep : ℝ) ≤ W.card by nlinarith [hWlo])
  obtain ⟨r, hr, A, _hAprior, hAτ, h3A, h4A, hPc, hBudget⟩ :=
    hPrepared (restrictedHost H (univ \ W)) F hNPrep h3W h4W
  have hWcard : Fintype.card (Survivors (univ \ W)) = W.card :=
    CorePaid.card_survivors_compl W
  have hAτ' : (A.card : ℝ) ≤ τPrep * W.card := by
    simpa only [hWcard] using hAτ
  have hBudget' : K (β r) *
      (ξSample + (A.card : ℝ) * C / (q * W.card)) ≤
      1 / (8 * C) := by
    simpa only [hWcard] using hBudget
  have h3A' : CommonNbrCond
      (restrictedHost (restrictedHost H (univ \ W)) A) F
      (αW / 2) := by
    convert h3A using 1
  have h4A' : HingeCond
      (restrictedHost (restrictedHost H (univ \ W)) A) F
      (αW / 2) h := by
    convert h4A using 1
  have hPc' : Dispersal.PreparedCore
      (restrictedHost (restrictedHost H (univ \ W)) A).G
      (restrictedHost (restrictedHost H (univ \ W)) A).lab
      F (αW / 4) h N (β r) := by
    convert hPc using 1
  exact ⟨W, A, r, hr, hWlo, hWhi, hRoute, hRaw, hAτ',
    h3A', h4A', hPc', hBudget'⟩

#print axioms uniform_sampled_paid_schedule_before_host

end TypedTriangle.Vortex
