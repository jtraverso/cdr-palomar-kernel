/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3ResourceUnionBudget
public import RequestProject.TypedTriangle.FixedSampleAmbientAvoidance
public import RequestProject.TypedTriangle.SampledBasalLift
public import RequestProject.TypedTriangle.SlotPairing
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Assemble a sampled dense reference with four already constructed basal
resource families. The resource degree is paid in the reference window, and
the lifted reference remains disjoint from their union. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open SelSimul SampledResource

theorem dense_reference_for_four_basal_resources {I : Type}
    (F : Set (Multiset I)) (C q β η : ℝ) (h : ℕ)
    (hC : 1 ≤ C) (hq : 0 < q) (hβ : 0 < β) (hη : 0 < η) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ ξ : ℝ, 0 < ξ →
      ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧ ∃ n₀ : ℕ,
        ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
          (W : Finset V) (A B C₀ D : Finset (Sym2 V))
          (ρ τ ηT εBank : ℝ),
          n₀ ≤ W.card → IsDiffuseSeed H F C φ →
          q*Fintype.card V/2 ≤ W.card →
          (W.card : ℝ) < 2*q*Fintype.card V →
          (∀ u v, H.G.Adj u v →
            |S07V48.sampW H.G H.lab F φ W u v/q-1| ≤ ε) →
          letI : DecidableEq {x // x ∈ W} := Classical.decEq _
          let J : Host {x // x ∈ W} I :=
            ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
          HingeCond J F β h →
          ρ+τ+ηT ≤ γ*q/8 → εBank ≤ γ/4 →
          (∀ v, (degIn A v:ℝ) ≤ ρ*Fintype.card V) →
          (∀ v, (degIn B v:ℝ) ≤ τ*Fintype.card V) →
          (∀ v, (degIn C₀ v:ℝ) ≤ ηT*Fintype.card V) →
          (∀ v, (degIn D v:ℝ) ≤ εBank*W.card) →
          2 ≤ γ*W.card →
          Basal H F (((A∪B)∪C₀)∪D) →
          ∃ E₀ D₀, E₀ ⊆ edges J ∧ IsDecomposition J F E₀ D₀ ∧
            Disjoint (lift W E₀) (((A∪B)∪C₀)∪D) ∧
            Basal H F (((((A∪B)∪C₀)∪D)∪lift W E₀)) ∧
            ∀ v, (SparseEdge.degIn (edges J\E₀) v:ℝ) ≤ η*W.card := by
  obtain ⟨θ,hθ,hRef⟩ := RawReference.dense_reference_avoiding_ambient
    F C q β η h hC hq hβ hη
  refine ⟨θ,hθ,?_⟩
  intro ξ hξ
  obtain ⟨ε,γ,hε,hγ,n₀,hRef'⟩ := hRef ξ hξ
  refine ⟨ε,γ,hε,hγ,n₀,?_⟩
  intro V _ H φ W A B C₀ D ρ τ ηT εBank hn hSeed hWlo hWhi hRaw
  letI : DecidableEq {x // x ∈ W} := Classical.decEq _
  intro J hJ4 hSum hBank hA hB hC₀ hD hLarge hBasal
  let U := (((A∪B)∪C₀)∪D)
  obtain ⟨dU,hUd,hUcap⟩ := four_resource_reference_window
    W A B C₀ D q γ ρ τ ηT εBank hq hγ hWlo hSum hBank
    hA hB hC₀ hD hLarge
  obtain ⟨E₀,D₀,hE,hDec,hAvoid,hHole⟩ :=
    hRef' H φ W U dU hn hSeed hWlo hWhi hRaw hJ4 hUd hUcap
  have hEbasal : Basal H F (lift W E₀) :=
    SampledResource.basal_lift H F W ⟨D₀,hDec⟩
  have hUnion : Basal H F (U∪lift W E₀) :=
    Basal.union hBasal hEbasal hAvoid.symm
  exact ⟨E₀,D₀,hE,hDec,hAvoid,hUnion,hHole⟩

#print axioms dense_reference_for_four_basal_resources

end TypedTriangle.CatalogNative
