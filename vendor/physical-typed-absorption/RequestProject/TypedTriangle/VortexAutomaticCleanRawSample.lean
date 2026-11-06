/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexCleanRawProfileSampling
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex
open RawReference CorePaid

/-- One automatic-precision sample retains all external-root geometry tests,
the approximate fractional profile, and a polynomial family of additional
tests with a fixed exponential tail (in particular the native path tests). -/
theorem exists_automatic_clean_raw_profile_tests_uniform
    (αmin q b θExtra : ℝ) (h : ℕ)
    (hαmin : 0 < αmin) (hq : 0 < q) (hq1 : q ≤ 1)
    (hb : 0 < b) (hExtraPos : 0 < θExtra) :
    ∃ N : ℝ, ∀ {V I : Type*} [Fintype V] (H : Host V I)
      (F : Set (Multiset I)) (α ε : ℝ),
      αmin ≤ α → ε ≤ 1/2 → N ≤ (Fintype.card V : ℝ) →
      CommonNbrCond H F α → ∀ hClean : CleanHingeCond H F α h,
      ∀ μ : Finset V → ℝ,
        (∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b/Fintype.card V) →
        (∀ e ∈ edges H, |bdry H F μ e-1| ≤ ε) →
      ∀ {J : Type*} [Fintype J], Fintype.card J ≤ Fintype.card V ^ 3 →
      ∀ E : J → Finset V → Prop,
        (∀ j, bprob q univ (E j) ≤ Real.exp (-(θExtra * Fintype.card V))) →
      let η : ℝ := (Real.sqrt (Real.sqrt (Fintype.card V : ℝ)))⁻¹
      0 < η ∧ η < 1 ∧ ∃ W : Finset V,
        (1-η)*q*Fintype.card V ≤ W.card ∧
        (W.card : ℝ) < (1+η)*q*Fintype.card V ∧
        (∀ u v, u ≠ v → ∀ k, ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
          (1-η)*α*q*Fintype.card V ≤ ((commonNbrs H k u v) ∩ W).card) ∧
        (∀ u v a c, HingeTest H.G H.lab F u v a c →
          (1-η)*α*q^(cleanHingeOrder hClean u v a c-4)*
            (Fintype.card V : ℝ)^(cleanHingeOrder hClean u v a c-4) ≤
              (((SparseEdge.hinges H.G H.lab F u v a c
                (cleanHingeOrder hClean u v a c)).filter (fun K => s(a,c) ∉ K)).filter
                  (fun K => freeV u v a c K ⊆ W)).card) ∧
        (∀ u v, H.G.Adj u v →
          |S07V48.sampW H.G H.lab F μ W u v/q-1| ≤ ε+2*η) ∧
        ∀ j, ¬ E j W := by
  obtain ⟨c₀,N₀,hc₀,hGeom⟩ :=
    exists_anchored_sampling_parameters αmin q h hαmin hq
  let c := min c₀ (min (q^2/(8*b)) θExtra)
  have hc : 0 < c := lt_min hc₀ (lt_min (by positivity) hExtraPos)
  obtain ⟨Nbudget,hBudget⟩ := polynomial_sqrt_budget 6 c hc
  refine ⟨max N₀ (max Nbudget 3),?_⟩
  intro V I _ H F α ε hαge hε hn h3 hClean μ hμ hLoad J _ hJ E hE
  have hN₀ : N₀ ≤ (Fintype.card V : ℝ) := (le_max_left _ _).trans hn
  have hNbudget : Nbudget ≤ (Fintype.card V : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn3 : (3 : ℝ) ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn0 : 0 < Fintype.card V := by exact_mod_cast (by linarith : (0 : ℝ) < Fintype.card V)
  obtain ⟨hη,hη1,hSize,hPool,hHinge,-⟩ := hGeom (Fintype.card V) hN₀
  let η : ℝ := (Real.sqrt (Real.sqrt (Fintype.card V : ℝ)))⁻¹
  let θ := c*η^2
  have hc₀le : c ≤ c₀ := min_le_left _ _
  have hcRaw : c ≤ q^2/(8*b) := (min_le_right _ _).trans (min_le_left _ _)
  have hcExtra : c ≤ θExtra := (min_le_right _ _).trans (min_le_right _ _)
  have hθ₀ : θ ≤ c₀*η^2 := mul_le_mul_of_nonneg_right hc₀le (sq_nonneg _)
  have hθraw : θ ≤ η^2*q^2/(8*b) := by
    have h := mul_le_mul_of_nonneg_right hcRaw (sq_nonneg η)
    convert h using 1 <;> ring
  have hηsq : η^2 ≤ 1 := by nlinarith [hη,hη1]
  have hθExtra : θ ≤ θExtra :=
    (mul_le_of_le_one_right hc.le hηsq).trans hcExtra
  have hExtraTail : ∀ j, bprob q univ (E j) ≤ Real.exp (-(θ*Fintype.card V)) := by
    intro j
    exact (hE j).trans (Real.exp_le_exp.mpr
      (neg_le_neg (mul_le_mul_of_nonneg_right hθExtra (by positivity))))
  have hCount : (Fintype.card
      ((((V × V × V) ⊕ (V × V × V × V)) ⊕ (V × V × Bool)) ⊕ J) : ℝ) ≤
      (Fintype.card V : ℝ)^4 + 2*(Fintype.card V : ℝ)^3 +
        2*(Fintype.card V : ℝ)^2 := by
    have hJR : (Fintype.card J : ℝ) ≤ (Fintype.card V : ℝ)^3 := by exact_mod_cast hJ
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith
  have hPoly : (Fintype.card V : ℝ)^4 + 2*(Fintype.card V : ℝ)^3 +
      2*(Fintype.card V : ℝ)^2 ≤ (Fintype.card V : ℝ)^6 := by
    have hn1 : (1 : ℝ) ≤ Fintype.card V := by linarith
    have hp34 : (Fintype.card V : ℝ)^3 ≤ (Fintype.card V : ℝ)^4 :=
      pow_le_pow_right₀ hn1 (by decide)
    have hp24 : (Fintype.card V : ℝ)^2 ≤ (Fintype.card V : ℝ)^4 :=
      pow_le_pow_right₀ hn1 (by decide)
    have hnSq : (5 : ℝ) ≤ (Fintype.card V : ℝ)^2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hnSq
      (show (0 : ℝ) ≤ (Fintype.card V : ℝ)^4 by positivity)
    nlinarith
  have hBudget' : (Fintype.card
      ((((V × V × V) ⊕ (V × V × V × V)) ⊕ (V × V × Bool)) ⊕ J)+2 : ℝ)*
        Real.exp (-(θ*Fintype.card V)) < 1 := by
    have hRate : (c * (Real.sqrt (Real.sqrt (Fintype.card V : ℝ)))⁻¹ ^ 2) *
        Fintype.card V = c * Real.sqrt (Fintype.card V : ℝ) := by
      have hs : 0 < Real.sqrt (Fintype.card V : ℝ) :=
        Real.sqrt_pos.mpr (by exact_mod_cast hn0)
      have hsq : (Real.sqrt (Fintype.card V : ℝ)) ^ 2 = Fintype.card V :=
        Real.sq_sqrt (by positivity)
      rw [inv_pow, Real.sq_sqrt hs.le]
      calc
        c * (Real.sqrt (Fintype.card V : ℝ))⁻¹ * Fintype.card V =
            c * (Real.sqrt (Fintype.card V : ℝ))⁻¹ *
              (Real.sqrt (Fintype.card V : ℝ)) ^ 2 := by rw [hsq]
        _ = c * Real.sqrt (Fintype.card V : ℝ) := by field_simp [hs.ne']
    have hp := hBudget (Fintype.card V) hNbudget
    have hFinal := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (add_le_add (hCount.trans hPoly) (le_refl (2 : ℝ)))
        (Real.exp_pos (-(c*Real.sqrt (Fintype.card V)))).le)
      (by simpa only [neg_mul] using hp)
    simpa only [θ,η,hRate,neg_mul] using hFinal
  obtain ⟨W,hWlo,hWhi,hPoolW,hHingeW,hRawW,hTests⟩ :=
    anchored_clean_raw_profile_tests_at_rate H F α q η θ b ε h
      (lt_of_lt_of_le hαmin hαge) hq hq1 hη hη1 hn0 hb hε μ hμ hLoad h3 hClean
      (hθ₀.trans hSize) (hθ₀.trans (hPool.trans (by gcongr)))
      (fun i hi6 hih => hθ₀.trans ((hHinge i hi6 hih).trans (by gcongr)))
      hθraw E hExtraTail hBudget'
  have hηlt : η < 1 := by
    have hn1 : (1 : ℝ) < Fintype.card V := by linarith
    have hs : (1 : ℝ) < Real.sqrt (Fintype.card V : ℝ) := by
      simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hn1
    have hss : (1 : ℝ) < Real.sqrt (Real.sqrt (Fintype.card V : ℝ)) := by
      simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hs
    exact inv_lt_one_of_one_lt₀ hss
  exact ⟨hη,hηlt,W,hWlo,hWhi,hPoolW,hHingeW,hRawW,hTests⟩

#print axioms exists_automatic_clean_raw_profile_tests_uniform
end TypedTriangle.Vortex
