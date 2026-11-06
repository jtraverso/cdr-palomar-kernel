/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexGlobalRawProfileBudget
public import RequestProject.TypedTriangle.VortexSurvivorRawSampleWeights
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open RawReference

def RawProfileAt {V I : Type*} [Fintype V] (H : Host V I)
    (F : Set (Multiset I)) (C ρ : ℝ) (μ : Finset V → ℝ) : Prop :=
  (∀ T, IsAllowed H F T → ((1 - ρ) / C) / Fintype.card V ≤ μ T ∧
    μ T ≤ ((1 + ρ) * C) / Fintype.card V) ∧
  ∀ e ∈ edges H, |bdry H F μ e - 1| ≤ ρ

theorem RawProfileAt.mono {V I : Type*} [Fintype V] {H : Host V I}
    {F : Set (Multiset I)} {C ρ σ : ℝ} {μ : Finset V → ℝ}
    (hRaw : RawProfileAt H F C ρ μ) (hC : 0 ≤ C) (hρσ : ρ ≤ σ) :
    RawProfileAt H F C σ μ := by
  constructor
  · intro T hT
    have h := hRaw.1 T hT
    have hLo : (1 - σ) / C ≤ (1 - ρ) / C :=
      div_le_div_of_nonneg_right (by linarith) hC
    have hHi : (1 + ρ) * C ≤ (1 + σ) * C :=
      mul_le_mul_of_nonneg_right (by linarith) hC
    exact ⟨(div_le_div_of_nonneg_right hLo (by positivity)).trans h.1,
      h.2.trans (div_le_div_of_nonneg_right hHi (by positivity))⟩
  · intro e he
    exact (hRaw.2 e he).trans hρσ

theorem globalRawProfileError_nonneg (E : ℝ) (β : ℕ → ℝ)
    (hE : 0 ≤ E) (hβ : ∀ j, 0 ≤ β j) (n : ℝ) (r : ℕ) :
    0 ≤ globalRawProfileError 4 E β n r := by
  exact add_nonneg (mul_nonneg (by norm_num) (automaticRelativeError_nonneg n))
    (mul_nonneg hE (sum_nonneg (by intro j _; exact hβ j)))

theorem raw_profile_restrict_global {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (C E : ℝ) (β : ℕ → ℝ)
    (μ : Finset V → ℝ) (r s : ℕ) (A : Finset V) (δ : ℝ)
    (hC : 0 < C) (hE1 : 1 ≤ E) (hEC : 2 * C ≤ E) (hβ : ∀ j, 0 ≤ β j)
    (hn : 0 < (Fintype.card V : ℝ))
    (hRaw : RawProfileAt H F C (globalRawProfileError 4 E β (Fintype.card V) r) μ)
    (hCap : globalRawProfileError 4 E β (Fintype.card V) r ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hA : (A.card : ℝ) ≤ δ * Fintype.card V)
    (hIndex : δ ≤ (∑ j ∈ range s, β j) - ∑ j ∈ range r, β j) :
    RawProfileAt (restrictedHost H A) F C
      (globalRawProfileError 4 E β (Fintype.card (Survivors A)) s) (restrictedWeights μ A) := by
  let ρ := globalRawProfileError 4 E β (Fintype.card V) r
  have hE : 0 ≤ E := by linarith
  have hρ : 0 ≤ ρ := globalRawProfileError_nonneg E β hE hβ _ r
  have hOut := restricted_raw_profile_with_additive_error H F μ C ρ ρ δ
    hC hρ hCap hδ hδ1 hn hRaw.1 hRaw.2 A hA
  have hcR : (Fintype.card (Survivors A) : ℝ) + A.card = Fintype.card V := by
    exact_mod_cast card_survivors_add_card A
  have hPos : (0 : ℝ) < Fintype.card (Survivors A) := by
    have hs : (1 - δ) * Fintype.card V ≤ (Fintype.card (Survivors A) : ℝ) := by linarith
    exact (mul_pos (by linarith) hn).trans_le hs
  have hSize : (Fintype.card (Survivors A) : ℝ) ≤ Fintype.card V := by
    linarith [(by positivity : (0 : ℝ) ≤ A.card)]
  have hCoef := globalRawProfileError_prepare 4 E 1 δ β (by norm_num) hE hE1 hδ
    (Fintype.card V) (Fintype.card (Survivors A)) r s hPos hSize hIndex
  have hLoad := globalRawProfileError_prepare 4 E (2 * C) δ β (by norm_num) hE hEC hδ
    (Fintype.card V) (Fintype.card (Survivors A)) r s hPos hSize hIndex
  constructor
  · intro T hT
    have h := hOut.1 T hT
    have hLo : (1 - globalRawProfileError 4 E β (Fintype.card (Survivors A)) s) / C ≤
        (1 - (ρ + δ)) / C := div_le_div_of_nonneg_right (by dsimp [ρ] at *; linarith) hC.le
    have hHi : (1 + (ρ + δ)) * C ≤
        (1 + globalRawProfileError 4 E β (Fintype.card (Survivors A)) s) * C :=
      mul_le_mul_of_nonneg_right (by dsimp [ρ] at *; linarith) hC.le
    exact ⟨(div_le_div_of_nonneg_right hLo (by positivity)).trans h.1,
      h.2.trans (div_le_div_of_nonneg_right hHi (by positivity))⟩
  · intro e he
    have hCoeff : (1 + ρ) * C * δ ≤ (2 * C) * δ := by
      have hs := mul_le_mul_of_nonneg_right (show 1 + ρ ≤ 2 by linarith) hC.le
      exact mul_le_mul_of_nonneg_right hs hδ
    exact (hOut.2 e he).trans (by dsimp [ρ] at *; linarith)

theorem raw_profile_sample_global {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (C E q : ℝ) (β : ℕ → ℝ)
    (μ : Finset V → ℝ) (r s : ℕ) (W : Finset V)
    (hC : 0 < C) (hE : 0 ≤ E) (hq : 0 < q) (hβ : ∀ j, 0 ≤ β j)
    (hn : 0 < (Fintype.card V : ℝ)) (hη : automaticRelativeError (Fintype.card V) < 1)
    (hRaw : RawProfileAt H F C (globalRawProfileError 4 E β (Fintype.card V) r) μ)
    (hCap : globalRawProfileError 4 E β (Fintype.card V) r ≤ 1)
    (hWlo : (1 - automaticRelativeError (Fintype.card V)) * q * Fintype.card V ≤ W.card)
    (hWhi : (W.card : ℝ) ≤ (1 + automaticRelativeError (Fintype.card V)) * q * Fintype.card V)
    (hShrink : 16 * W.card ≤ Fintype.card V) (hIndex : r ≤ s)
    (hProfile : ∀ u v, H.G.Adj u v →
      |S07V48.sampW H.G H.lab F μ W u v / q - 1| ≤
        globalRawProfileError 4 E β (Fintype.card V) r + 2 * automaticRelativeError (Fintype.card V)) :
    RawProfileAt (restrictedHost H (univ \ W)) F C
      (globalRawProfileError 4 E β (Fintype.card (Survivors (univ \ W))) s)
      (survivorSampledWeights μ W q) := by
  let ρ := globalRawProfileError 4 E β (Fintype.card V) r
  let η := automaticRelativeError (Fintype.card V)
  have hρ : 0 ≤ ρ := globalRawProfileError_nonneg E β hE hβ _ r
  have hOut := survivor_sampled_raw_profile_with_additive_error H F μ C q ρ η (ρ + 2 * η)
    hC hq hρ hCap (automaticRelativeError_nonneg _) hη hn hRaw.1 W hWlo hWhi hProfile
  have hWpos : (0 : ℝ) < W.card :=
    (mul_pos (mul_pos (by dsimp [η] at *; linarith) hq) hn).trans_le hWlo
  have h16R : (16 : ℝ) * W.card ≤ Fintype.card V := by exact_mod_cast hShrink
  have hError := globalRawProfileError_sample 4 E β (by norm_num) hE hβ
    (Fintype.card V) W.card r s hn hWpos h16R hIndex
  have hRawOut : RawProfileAt (restrictedHost H (univ \ W)) F C (ρ + 2 * η)
      (survivorSampledWeights μ W q) := hOut
  apply hRawOut.mono hC.le
  simpa only [CorePaid.card_survivors_compl, ρ, η] using hError

#print axioms raw_profile_restrict_global
#print axioms raw_profile_sample_global
end TypedTriangle.Vortex
