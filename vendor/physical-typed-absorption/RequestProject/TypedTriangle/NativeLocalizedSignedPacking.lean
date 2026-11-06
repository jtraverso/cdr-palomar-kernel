/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SignedEnvelopePacking
public import RequestProject.TypedTriangle.LocalizedSeedMass
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedStar

/-- A native signed nibble at the LOCAL n|Z| scale. The linear lower mass is
derived from H1/H3 when Z meets an active root; every other test is identically
zero. No density assumption on Z and no global quadratic error are introduced. -/
theorem localized_signed_packing_of_H1H3 (C α η τ L : ℝ) (q : ℕ)
    (hC : 0 < C) (hα : 0 < α) (hη : 0 < η) (hτ : 0 < τ) (hL : 0 < L) :
    ∃ n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      CommonNbrCond H F α → ∀ (κ : Type) [Fintype κ]
      (bad : κ → Finset V) (W : κ → Finset V → ℝ),
      (Fintype.card κ:ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → |W k T| ≤ 3*L*(T∩bad k).card) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        ∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed H F, φ T*W k T)| ≤
          τ*Fintype.card V*(bad k).card := by
  obtain ⟨n₀,hPack⟩ := signed_envelope_sparse_packing C α (α/6) η (6*τ) (9*L) q
    hC hα (by positivity) hη (by positivity) (by positivity)
  refine ⟨n₀,?_⟩
  intro V I _ H F φ hn hφ h3 κ _ bad W hκ hW
  let AK := {k : κ // ∃ v ∈ bad k, ActiveRoot H F v}
  have hAK : (Fintype.card AK:ℝ) ≤ (Fintype.card V:ℝ)^q :=
    (show (Fintype.card AK:ℝ) ≤ Fintype.card κ by
      exact_mod_cast (Fintype.card_subtype_le (fun k => ∃ v ∈ bad k, ActiveRoot H F v))).trans hκ
  have hA : ∀ k : AK, ∀ T, IsAllowed H F T →
      0 ≤ localEnvelope (bad k.1) T ∧ localEnvelope (bad k.1) T ≤ 1 ∧
        |W k.1 T| ≤ (9*L)*localEnvelope (bad k.1) T := by
    intro k T hT
    obtain ⟨hA0,hA1⟩ := localEnvelope_bounds (bad k.1) hT
    refine ⟨hA0,hA1,?_⟩
    have hh := hW k.1 T hT
    unfold localEnvelope
    nlinarith only [hh]
  obtain ⟨P,hPsub,hP,hSparse,hQuota⟩ := hPack H F φ hn hφ h3 AK
    (fun k => localEnvelope (bad k.1)) (fun k => W k.1) hAK hA
    (fun k => (localEnvelope_mass_bounds H F φ hC hφ h3 (bad k.1) k.2).1)
  refine ⟨P,hPsub,hP,hSparse,?_⟩
  intro k
  by_cases hk : ∃ v ∈ bad k, ActiveRoot H F v
  · have hQ := hQuota ⟨k,hk⟩
    have hM := (localEnvelope_mass_bounds H F φ hC hφ h3 (bad k) hk).2
    have hs := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 6*τ)
    exact hQ.trans (by nlinarith only [hs])
  · have hzero : ∀ T, IsAllowed H F T → W k T = 0 := by
      intro T hT
      have he : T∩bad k = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        obtain ⟨hvT,hvbad⟩ := mem_inter.mp hv
        exact hk ⟨v,hvbad,T,hT,hvT⟩
      have hh := hW k T hT
      rw [he,card_empty,Nat.cast_zero,mul_zero] at hh
      exact abs_nonpos_iff.mp hh
    have hsel : (∑ T ∈ P, W k T) = 0 :=
      sum_eq_zero fun T hT => hzero T (isAllowed_of_mem_allowed (hPsub hT))
    have hseed : (∑ T ∈ allowed H F, φ T*W k T) = 0 :=
      sum_eq_zero fun T hT => by rw [hzero T (isAllowed_of_mem_allowed hT),mul_zero]
    rw [hsel,hseed,sub_self,abs_zero]
    positivity

end TypedTriangle.WeightedStar
