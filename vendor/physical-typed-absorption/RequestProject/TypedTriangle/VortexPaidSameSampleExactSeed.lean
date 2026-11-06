/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4SameSampleH1Bridge
public import RequestProject.TypedTriangle.VortexExplicitDecidableExactSeed
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex


/-- The inverse budget is split between sampling error and the paid holes. -/
theorem same_sample_paid_inverse_budget (C K ξ η n : ℝ) (d : ℕ)
    (hC : 1 ≤ C) (hK : 0 ≤ K) (hn : 0 < n)
    (hd : (d : ℝ) ≤ η * n)
    (hSample : K * ξ ≤ 1 / (8 * C))
    (hHoles : K * (4 * C * η) ≤ 1 / (8 * C)) :
    K * (ξ + 2 * (2 * C) * d / n) ≤ 1 / (4 * C) := by
  have hD : (4 * C) * (d : ℝ) ≤ (4 * C) * (η * n) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  have hTerm : 2 * (2 * C) * (d : ℝ) / n ≤ 4 * C * η := by
    apply (div_le_iff₀ hn).2
    nlinarith
  have hScaled := mul_le_mul_of_nonneg_left hTerm hK
  calc
    K * (ξ + 2 * (2 * C) * d / n) =
        K * ξ + K * (2 * (2 * C) * d / n) := by ring
    _ ≤ K * ξ + K * (4 * C * η) :=
      add_le_add (le_refl _) hScaled
    _ ≤ 1 / (4 * C) := by
      have hCpos : (0 : ℝ) < C := by linarith
      rw [show (1 / (4 * C) : ℝ) = 1 / (8 * C) + 1 / (8 * C) by
        field_simp; ring]
      exact add_le_add hSample hHoles

/-- Exact H1 on the actual paid child from the same sampled reference.
The geometry, physical indicator and smooth inverse are explicit premises. -/
theorem paid_child_same_sample_exact_seed {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (φ : Finset V → ℝ)
    (W : Finset V) (q C ξ η Kinv : ℝ)
    (E₀ : Finset (Sym2 {x // x ∈ W}))
    (D₀ : Finset (Finset {x // x ∈ W}))
    (Ytot : Finset (Sym2 V))
    (hC : 1 ≤ C) (hq : 0 < q) (hξ : 0 ≤ ξ) (hη : 0 ≤ η)
    (hK : 0 ≤ Kinv) (hWpos : 0 < W.card)
    (hSeed : IsDiffuseSeed H F C φ)
    (hWlo : q * Fintype.card V / 2 ≤ W.card)
    (hWhi : (W.card : ℝ) < 2 * q * Fintype.card V)
    (hProfile : ∀ u v, H.G.Adj u v →
      |S07V48.sampW H.G H.lab F φ W u v / q - 1| ≤ ξ)
    (hEDec : IsDecomposition
      (⟨H.G.comap Subtype.val, H.lab ∘ Subtype.val⟩ :
        Host {x // x ∈ W} I) F E₀ D₀)
    (hYtotE : Ytot ⊆ edges H)
    (hHole : ∀ v : {x // x ∈ W},
      (SparseEdge.degIn
        (edges (⟨H.G.comap Subtype.val, H.lab ∘ Subtype.val⟩ :
          Host {x // x ∈ W} I) \ E₀) v : ℝ) ≤ η * W.card)
    (hSampleBudget : Kinv * ξ ≤ 1 / (8 * C))
    (hHoleBudget : Kinv * (4 * C * η) ≤ 1 / (8 * C)) :
    letI : DecidableEq {x // x ∈ W} := fun a b => a.instDecidableEq b
    let J : Host {x // x ∈ W} I :=
      ⟨H.G.comap Subtype.val, H.lab ∘ Subtype.val⟩
    let Echild := E₀ ∪ SampledResource.pull W Ytot
    let K := subHost J Echild
    NativeSmooth.Smooth K F Kinv →
    IsPhysical K F (edges K) →
    ∃ ψ : Finset {x // x ∈ W} → ℝ,
      IsDiffuseSeed K F (4 * C) ψ := by
  letI : DecidableEq {x // x ∈ W} := fun a b => a.instDecidableEq b
  dsimp only
  intro hSmooth hPhysical
  obtain ⟨μ, hSupport, hWeights, hLoad, hd⟩ :=
    CatalogNative.paid_child_same_sample_approx_seed H F φ W q C ξ η
      E₀ D₀ Ytot (by linarith) hq hη hSeed hWlo hWhi
      hProfile hEDec hYtotE hHole
  let J : Host {x // x ∈ W} I :=
    ⟨H.G.comap Subtype.val, H.lab ∘ Subtype.val⟩
  let Echild := E₀ ∪ SampledResource.pull W Ytot
  let K := subHost J Echild
  let d := ⌊η * W.card⌋₊
  have hbudget : Kinv *
      (ξ + 2 * (2 * C) * d / Fintype.card {x // x ∈ W}) ≤
      1 / (4 * C) := by
    have hn : (0 : ℝ) < Fintype.card {x // x ∈ W} := by
      simpa only [Fintype.card_subtype_compl, Fintype.card_coe] using
        (show (0 : ℝ) < W.card by exact_mod_cast hWpos)
    have hd' : (d : ℝ) ≤ η * Fintype.card {x // x ∈ W} := by
      simpa only [Fintype.card_coe] using hd
    exact same_sample_paid_inverse_budget C Kinv ξ η
      (Fintype.card {x // x ∈ W}) d hC hK hn hd'
      hSampleBudget hHoleBudget
  have hSupportK : ∀ T, μ T ≠ 0 → IsAllowed K F T := by
    simpa only [K, Echild, J] using hSupport
  have hWeightsK : ∀ T, IsAllowed K F T →
      (1 / (2 * C)) / Fintype.card {x // x ∈ W} ≤ μ T ∧
        μ T ≤ (2 * C) / Fintype.card {x // x ∈ W} := by
    simpa only [K, Echild, J] using hWeights
  have hLoadK : ∀ e ∈ edges K,
      |bdry K F μ e - 1| ≤
        ξ + 2 * (2 * C) * d / Fintype.card {x // x ∈ W} := by
    simpa only [K, Echild, J, d] using hLoad
  exact exact_seed_on_fixed_host_of_smooth_explicit K F C Kinv
    (ξ + 2 * (2 * C) * d / Fintype.card {x // x ∈ W})
    hC (by positivity) hSmooth hPhysical μ hSupportK hWeightsK hLoadK hbudget

#print axioms same_sample_paid_inverse_budget
#print axioms paid_child_same_sample_exact_seed

end TypedTriangle.Vortex
