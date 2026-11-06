/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4SameSampleApproxSeed
public import RequestProject.TypedTriangle.G4PaidReferenceEdgePull
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! The actual paid child inherits an approximate seed from the *same*
sampled reference. Its hole budget is the one exported by the G4 layer. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

theorem paid_child_same_sample_approx_seed {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (φ : Finset V → ℝ)
    (W : Finset V) (q C ξ η : ℝ)
    (E₀ : Finset (Sym2 {x // x ∈ W}))
    (D₀ : Finset (Finset {x // x ∈ W}))
    (Ytot : Finset (Sym2 V))
    (hC : 0 < C) (hq : 0 < q) (hη : 0 ≤ η)
    (hSeed : IsDiffuseSeed H F C φ)
    (hWlo : q*Fintype.card V/2 ≤ W.card)
    (hWhi : (W.card:ℝ) < 2*q*Fintype.card V)
    (hProfile : ∀ u v, H.G.Adj u v →
      |S07V48.sampW H.G H.lab F φ W u v/q-1| ≤ ξ)
    (hEDec : IsDecomposition
      (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ :
        Host {x // x ∈ W} I) F E₀ D₀)
    (hYtotE : Ytot ⊆ edges H)
    (hHole : ∀ v : {x // x ∈ W},
      (SparseEdge.degIn
        (edges (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ :
          Host {x // x ∈ W} I) \ E₀) v : ℝ) ≤ η*W.card) :
    let J : Host {x // x ∈ W} I :=
      ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
    let Echild := E₀ ∪ SampledResource.pull W Ytot
    let K := subHost J Echild
    let d := ⌊η*W.card⌋₊
    ∃ μK : Finset {x // x ∈ W} → ℝ,
      (∀ T, μK T ≠ 0 → IsAllowed K F T) ∧
      (∀ T, IsAllowed K F T →
        (1/(2*C))/Fintype.card {x // x ∈ W} ≤ μK T ∧
          μK T ≤ (2*C)/Fintype.card {x // x ∈ W}) ∧
      (∀ e ∈ edges K,
        |bdry K F μK e-1| ≤
          ξ+2*(2*C)*d/Fintype.card {x // x ∈ W}) ∧
      (d:ℝ) ≤ η*W.card := by
  let J : Host {x // x ∈ W} I :=
    ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  let Echild := E₀ ∪ SampledResource.pull W Ytot
  let d := ⌊η*W.card⌋₊
  have hE₀ : E₀ ⊆ edges J := by
    intro e he
    obtain ⟨S,hS,heS⟩ := hEDec.exists_mem he
    exact triEdges_subset_edges (hEDec.1 S hS) heS
  have hY : SampledResource.pull W Ytot ⊆ edges J :=
    paid_pull_subset_sampled_edges H W Ytot hYtotE
  have hEchild : Echild ⊆ edges J := union_subset hE₀ hY
  have hD : (d:ℝ) ≤ η*W.card := Nat.floor_le (by positivity)
  have hHoleJ (v : {x // x ∈ W}) :
      (SparseEdge.degIn (edges J \ E₀) v : ℝ) ≤ η*W.card := by
    convert hHole v using 1
  have hdeg : ∀ v : {x // x ∈ W},
      TypedTriangle.degIn (edges J \ Echild) v ≤ d := by
    intro v
    have hIncl : edges J \ Echild ⊆ edges J \ E₀ := by
      intro e he
      exact mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,
        fun hc => (mem_sdiff.mp he).2 (mem_union_left _ hc)⟩
    have hReal : (TypedTriangle.degIn (edges J \ Echild) v : ℝ) ≤
        η*W.card := by
      have hC : (TypedTriangle.degIn (edges J \ Echild) v : ℝ) ≤
          SparseEdge.degIn (edges J \ E₀) v := by
        have hSparse : (SparseEdge.degIn (edges J \ Echild) v : ℝ) ≤
            SparseEdge.degIn (edges J \ E₀) v := by
          have hNat : SparseEdge.degIn (edges J \ Echild) v ≤
              SparseEdge.degIn (edges J \ E₀) v := by
            unfold SparseEdge.degIn
            apply Finset.card_le_card
            intro e he
            simp only [Finset.mem_filter, Finset.mem_sdiff] at he ⊢
            exact ⟨⟨he.1.1, fun hc => he.1.2 (mem_union_left _ hc)⟩, he.2⟩
          exact_mod_cast hNat
        simpa only [TypedTriangle.degIn, SparseEdge.degIn] using hSparse
      exact hC.trans (hHoleJ v)
    exact Nat.le_floor hReal
  have hdeg' : ∀ v : {x // x ∈ W},
      TypedTriangle.degIn
        (edges (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ :
          Host {x // x ∈ W} I) \ Echild) v ≤ d := by
    intro v
    convert hdeg v using 1
  obtain ⟨μK,hSupport,hWeights,hLoad⟩ :=
    sampled_paid_child_approx_seed H F φ W q C ξ Echild d
      hC hq hSeed hWlo hWhi hProfile hEchild hdeg'
  refine ⟨μK,?_,?_,?_,hD⟩
  · simpa only [Echild] using hSupport
  · simpa only [Echild] using hWeights
  · simpa only [Echild,d] using hLoad

#print axioms paid_child_same_sample_approx_seed

end TypedTriangle.CatalogNative
