/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExactBasalFullComplement
public import RequestProject.TypedTriangle.SampledReferenceDegree
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! The exact H1--H4 persistence theorem applies to the union of a sparse
basal resource with a dense reference confined to a small sampled core. -/

open Finset Classical
noncomputable section

namespace TypedTriangle

theorem exact_complement_after_sampled_reference {I : Type}
    (F : Set (Multiset I)) (C α : ℝ) (h : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hh : 6 ≤ h) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (W : Finset V) (U : Finset (Sym2 V))
        (E₀ : Finset (Sym2 {x // x ∈ W})) (dU : ℕ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → CommonNbrCond H F α →
        HingeCond H F α h →
        Basal H F (U∪SampledResource.lift W E₀) →
        E₀ ⊆ edges
          (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ : Host {x // x ∈ W} I) →
        (∀ v, SparseEdge.degIn U v ≤ dU) →
        ((dU+W.card:ℕ):ℝ) ≤ ε*Fintype.card V →
        let B := U∪SampledResource.lift W E₀
        ∃ ψ : Finset V → ℝ,
          IsDiffuseSeed (subHost H (edges H\B)) F (2*C) ψ ∧
          IsPhysical (subHost H (edges H\B)) F
            (edges (subHost H (edges H\B))) ∧
          CommonNbrCond (subHost H (edges H\B)) F (α/2) ∧
          HingeCond (subHost H (edges H\B)) F
            (S07V49.hingeConstB α 1 h) (2*h-3) := by
  obtain ⟨ε,hε,n₀,hExact⟩ := exact_basal_full_complement F C α h hC hα hh
  refine ⟨ε,hε,n₀,?_⟩
  intro V _ H φ W U E₀ dU hn hSeed hPhys h3 h4 hBasal hE hU hSmall
  obtain ⟨DB,hDB⟩ := hBasal
  have hCover : BasalIncidence.cover DB = U∪SampledResource.lift W E₀ := hDB.2.2
  have hDegree : ∀ v, SparseEdge.degIn (BasalIncidence.cover DB) v ≤ dU+W.card := by
    intro v
    rw [hCover]
    exact SampledResource.full_reserved_degree_le H W U E₀ dU hU hE v
  have hDec : IsDecomposition H F (BasalIncidence.cover DB) DB := by
    simpa only [hCover] using hDB
  have hResult := hExact H φ DB (dU+W.card) hn hSeed hPhys h3 h4 hDec
    hDegree hSmall
  simpa only [hCover] using hResult

#print axioms exact_complement_after_sampled_reference

end TypedTriangle
