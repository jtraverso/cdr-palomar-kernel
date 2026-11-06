/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeDenseReference
public import RequestProject.TypedTriangle.SampledRawWeights
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! The dense reference constructor applies to a sampled core that has
already been fixed. It does not choose a new core after seeing the stock. -/

open Finset Classical
noncomputable section
namespace TypedTriangle.RawReference

theorem dense_reference_on_fixed_sample {I : Type} (F : Set (Multiset I))
    (C q β η : ℝ) (h : ℕ) (hC : 1 ≤ C) (hq : 0 < q)
    (hβ : 0 < β) (hη : 0 < η) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ ξ : ℝ, 0 < ξ →
      ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧ ∃ n₀ : ℕ,
        ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
          (W : Finset V),
          n₀ ≤ W.card → IsDiffuseSeed H F C φ →
          q*Fintype.card V/2 ≤ W.card →
          (W.card : ℝ) < 2*q*Fintype.card V →
          (∀ u v, H.G.Adj u v →
            |S07V48.sampW H.G H.lab F φ W u v/q-1| ≤ ε) →
          letI : DecidableEq {x // x ∈ W} := Classical.decEq _
          let J : Host {x // x ∈ W} I :=
            ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
          HingeCond J F β h →
          ∀ (S B : Finset (Sym2 {x // x ∈ W}))
            (DS : Finset (Finset {x // x ∈ W})) (dS dB : ℕ),
            S ⊆ edges J → IsDecomposition J F S DS → Disjoint S B →
            (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ θ*W.card →
            (∀ v, degIn B v ≤ dB) → (dB:ℝ) ≤ γ*W.card →
            ∃ E₀ D₀, S ⊆ E₀ ∧ E₀ ⊆ edges J ∧
              IsDecomposition J F E₀ D₀ ∧ DS ⊆ D₀ ∧
              Disjoint E₀ B ∧
              ∀ v, (degIn (edges J\E₀) v:ℝ) ≤ η*W.card := by
  have hCp : 0 < C := by linarith
  obtain ⟨θ,hθ,hRef⟩ := dense_reference_containing_stock F
    (1/(2*C)) (2*C) β h (by positivity)
    (by rw [div_le_iff₀ (by positivity : 0 < 2*C)]; nlinarith) hβ
  refine ⟨θ,hθ,?_⟩
  intro ξ hξ
  obtain ⟨εR,γ,hεR,hγ,nR,hReference⟩ := hRef η hη
  let ε := min εR ξ
  have hε : 0 < ε := lt_min hεR hξ
  refine ⟨ε,γ,hε,hγ,nR,?_⟩
  intro V _ H φ W hn hSeed hWlo hWhi hraw
  letI : DecidableEq {x // x ∈ W} := Classical.decEq _
  intro J hJ4 S B DS dS dB hS hDS hSB hSd hSs hBd hBs
  have hRaw := sampled_raw_profile hSeed hCp hq W hWlo hWhi
    (by intro u v huv; exact (hraw u v huv).trans (min_le_left _ _))
  have hResult := hReference J (sampledWeights φ W q)
    S B DS dS dB (by simpa only [Fintype.card_coe] using hn)
    hJ4 hRaw.1 hRaw.2 hS hDS hSB hSd
    (by simpa only [Fintype.card_coe] using hSs) hBd
    (by simpa only [Fintype.card_coe] using hBs)
  simpa only [Fintype.card_coe] using hResult

#print axioms dense_reference_on_fixed_sample

end TypedTriangle.RawReference
