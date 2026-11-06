/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.FixedSampleDenseReference
public import RequestProject.TypedTriangle.SampledForbiddenTransport
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! A dense child reference can avoid a prescribed ambient sparse resource.
This is still conditional on a prepared fixed core and its raw weight profile. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.RawReference

open SampledResource

theorem dense_reference_avoiding_ambient {I : Type} (F : Set (Multiset I))
    (C q β η : ℝ) (h : ℕ) (hC : 1 ≤ C) (hq : 0 < q)
    (hβ : 0 < β) (hη : 0 < η) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ ξ : ℝ, 0 < ξ →
      ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧ ∃ n₀ : ℕ,
        ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
          (W : Finset V) (B : Finset (Sym2 V)) (dB : ℕ),
          n₀ ≤ W.card → IsDiffuseSeed H F C φ →
          q*Fintype.card V/2 ≤ W.card →
          (W.card : ℝ) < 2*q*Fintype.card V →
          (∀ u v, H.G.Adj u v →
            |S07V48.sampW H.G H.lab F φ W u v/q-1| ≤ ε) →
          letI : DecidableEq {x // x ∈ W} := Classical.decEq _
          let J : Host {x // x ∈ W} I :=
            ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
          HingeCond J F β h →
          (∀ v, SparseEdge.degIn B v ≤ dB) →
          (dB:ℝ) ≤ γ*W.card →
          ∃ E₀ D₀, E₀ ⊆ edges J ∧ IsDecomposition J F E₀ D₀ ∧
            Disjoint (SampledResource.lift W E₀) B ∧
            ∀ v, (SparseEdge.degIn (edges J\E₀) v:ℝ) ≤ η*W.card := by
  obtain ⟨θ,hθ,hRef⟩ := dense_reference_on_fixed_sample F C q β η h
    hC hq hβ hη
  refine ⟨θ,hθ,?_⟩
  intro ξ hξ
  obtain ⟨ε,γ,hε,hγ,n₀,hRef'⟩ := hRef ξ hξ
  refine ⟨ε,γ,hε,hγ,n₀,?_⟩
  intro V _ H φ W B dB hn hSeed hWlo hWhi hRaw
  letI : DecidableEq {x // x ∈ W} := Classical.decEq _
  intro J hJ4 hBd hBsmall
  let B' := SampledResource.pull W B
  have hBd' : ∀ v : {x // x ∈ W}, SparseEdge.degIn B' v ≤ dB := by
    intro v
    change SelSimul.edeg B' v ≤ dB
    have hb : SelSimul.edeg B v.1 ≤ dB := by
      simpa only [SparseEdge.degIn, SelSimul.edeg] using hBd v.1
    simpa only [B', CorePayment.edeg_eq_classical] using
      (SampledResource.degree_pull_le W B v).trans hb
  have hEmpty : IsDecomposition J F ∅ (∅ : Finset (Finset {x // x ∈ W})) := by
    simp [IsDecomposition]
  obtain ⟨E₀,D₀,_,hE,hD,_,hDis,hHole⟩ :=
    hRef' H φ W hn hSeed hWlo hWhi hRaw hJ4
      ∅ B' ∅ 0 dB (empty_subset _) hEmpty (disjoint_empty_left B')
      (by intro v; simp [TypedTriangle.degIn])
      (by simpa only [Nat.cast_zero] using
        mul_nonneg hθ.le (Nat.cast_nonneg W.card)) hBd' hBsmall
  exact ⟨E₀,D₀,hE,hD,
    SampledResource.lift_disjoint_of_pull_disjoint W E₀ B hDis,hHole⟩

#print axioms dense_reference_avoiding_ambient

end TypedTriangle.RawReference
