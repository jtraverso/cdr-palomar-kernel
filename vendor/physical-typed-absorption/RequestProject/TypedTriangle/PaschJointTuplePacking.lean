module
public import RequestProject.TypedTriangle.PaschLocalizedTuplePacking
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
namespace TypedTriangle.Pasch
open WeightedStar
open LocalizedCover

/-- A single actual nibble controls the edge moments needed by the bank and
arbitrary bounded triangle statistics and the unoriented Pasch count. No lower mass assumption is imposed on
an individual triangle monitor. All families and eligible tuple tests share
the same packing. -/
theorem joint_packing_with_triangle_monitors_pasch_and_tuple_tests (C α η τ L σ : ℝ) (q : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η) (hτ : 0 < τ) (hL : 0 < L) (hσ : 0 < σ) :
    ∃ n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      CommonNbrCond H F α → ∀ (κ ι ν : Type) [Fintype κ] [Fintype ι] [Fintype ν]
      (bad : κ → Finset V) (loc : κ → Sym2 V → ℝ) (full : ι → Sym2 V → ℝ)
      (w : ν → Finset V → ℝ),
      ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*L*(T∩bad k).card) →
      (∀ k T, IsAllowed H F T → |triSum (full k) T| ≤ 3*L*T.card) →
      (∀ k T, IsAllowed H F T → |w k T| ≤ 1) →
      ∀ (ξ : Type) [Fintype ξ] (X : ℕ → ξ → Finset (Finset V) → ℝ),
      Fintype.card ξ ≤ (Fintype.card V)^q →
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ X ℓ k S) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        (∀ k, |edgeSum (loc k) (edges H\P.biUnion triEdges)| ≤ τ*Fintype.card V*(bad k).card) ∧
        (∀ k, |edgeSum (full k) (edges H\P.biUnion triEdges)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
        (∀ k, |(∑ T ∈ P, w k T)-(∑ T ∈ allowed H F, φ T*w k T)| ≤
          τ*(Fintype.card V:ℝ)^2) ∧
        |(count P:ℝ)-target φ (allowed H F)| ≤ σ*(Fintype.card V:ℝ)^2 ∧
        ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k : ξ,
          floorTupleTestControl (allowed H F) φ P (X ℓ k) ℓ := by
  obtain ⟨n₀,hPack⟩ := localized_signed_packing_with_pasch_and_tuple_tests C α η τ (L+1) σ q
    hC hα hη hτ (by positivity) hσ
  refine ⟨n₀,?_⟩
  intro V I _ H F φ hn hφ h3 κ ι ν _ _ _ bad loc full w hcard hloc hfull hw ξ _ X hξ hX
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
  obtain ⟨P,hPsub,hP,hSparse,hQuota,hPasch,hExtra⟩ :=
    hPack H F φ hn hφ h3 (κ ⊕ (ι ⊕ ν)) bad' wt hcard' hEnvelope ξ X hξ hX
  have hPE : P.biUnion triEdges ⊆ edges H := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  refine ⟨P,hPsub,hP,hSparse,?_,?_,?_,hPasch,hExtra⟩
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

#print axioms joint_packing_with_triangle_monitors_pasch_and_tuple_tests
end TypedTriangle.Pasch
