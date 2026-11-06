/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeLocalizedSignedPacking
public import RequestProject.TypedTriangle.SeedMoment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedStar
open LocalizedCover

/-- A single actual nibble controls the edge moments needed by the bank and
arbitrary bounded triangle statistics. No lower mass assumption is imposed on
an individual triangle monitor. All three families share the same packing. -/
theorem joint_sparse_packing_with_triangle_monitors (C α η τ L : ℝ) (q : ℕ)
    (hC : 0 < C) (hα : 0 < α) (hη : 0 < η) (hτ : 0 < τ) (hL : 0 < L) :
    ∃ n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      CommonNbrCond H F α → ∀ (κ ι ν : Type) [Fintype κ] [Fintype ι] [Fintype ν]
      (bad : κ → Finset V) (loc : κ → Sym2 V → ℝ) (full : ι → Sym2 V → ℝ)
      (w : ν → Finset V → ℝ),
      ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*L*(T∩bad k).card) →
      (∀ k T, IsAllowed H F T → |triSum (full k) T| ≤ 3*L*T.card) →
      (∀ k T, IsAllowed H F T → |w k T| ≤ 1) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        (∀ k, |edgeSum (loc k) (edges H\P.biUnion triEdges)| ≤ τ*Fintype.card V*(bad k).card) ∧
        (∀ k, |edgeSum (full k) (edges H\P.biUnion triEdges)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
        ∀ k, |(∑ T ∈ P, w k T)-(∑ T ∈ allowed H F, φ T*w k T)| ≤
          τ*(Fintype.card V:ℝ)^2 := by
  obtain ⟨n₀,hPack⟩ := localized_signed_packing_of_H1H3 C α η τ (L+1) q
    hC hα hη hτ (by positivity)
  refine ⟨n₀,?_⟩
  intro V I _ H F φ hn hφ h3 κ ι ν _ _ _ bad loc full w hcard hloc hfull hw
  let bad' : κ ⊕ (ι ⊕ ν) → Finset V := Sum.elim bad (fun _ => univ)
  let wt : κ ⊕ (ι ⊕ ν) → Finset V → ℝ :=
    Sum.elim (fun k T => triSum (loc k) T)
      (Sum.elim (fun k T => triSum (full k) T) w)
  have hcard' : (Fintype.card (κ ⊕ (ι ⊕ ν)):ℝ) ≤ (Fintype.card V:ℝ)^q := by
    simpa only [Fintype.card_sum,Nat.add_assoc] using hcard
  have hEnvelope : ∀ k T, IsAllowed H F T →
      |wt k T| ≤ 3*(L+1)*(T∩bad' k).card := by
    intro k T hT
    rcases k with k | (k | k)
    · exact (hloc k T hT).trans (by
        dsimp only [bad',Sum.elim_inl]
        have hc : (0:ℝ) ≤ (T∩bad k).card := Nat.cast_nonneg _
        nlinarith only [hc])
    · simpa only [wt,Sum.elim_inr,Sum.elim_inl,bad',inter_univ] using
        (hfull k T hT).trans (by
          have hc : (0:ℝ) ≤ T.card := Nat.cast_nonneg _
          nlinarith only [hc])
    · dsimp only [wt,Sum.elim_inr,bad']
      rw [inter_univ,hT.1]
      exact (hw k T hT).trans (by norm_num; linarith)
  obtain ⟨P,hPsub,hP,hSparse,hQuota⟩ :=
    hPack H F φ hn hφ h3 (κ ⊕ (ι ⊕ ν)) bad' wt hcard' hEnvelope
  have hPE : P.biUnion triEdges ⊆ edges H := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  refine ⟨P,hPsub,hP,hSparse,?_,?_,?_⟩
  · intro k
    exact remainder_moment_of_quota hφ P hP hPE (loc k)
      (τ*Fintype.card V*(bad k).card) (hQuota (.inl k))
  · intro k
    have hh := remainder_moment_of_quota hφ P hP hPE (full k)
      (τ*Fintype.card V*(univ : Finset V).card) (hQuota (.inr (.inl k)))
    simpa only [card_univ,pow_two,mul_assoc] using hh
  · intro k
    have hh := hQuota (.inr (.inr k))
    simpa only [wt,Sum.elim_inr,bad',card_univ,pow_two,mul_assoc] using hh

#print axioms joint_sparse_packing_with_triangle_monitors
end TypedTriangle.WeightedStar
