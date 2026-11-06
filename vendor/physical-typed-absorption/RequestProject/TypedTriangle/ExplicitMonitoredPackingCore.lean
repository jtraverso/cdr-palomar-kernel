module
public import RequestProject.TypedTriangle.ExplicitBankCore
public import RequestProject.TypedTriangle.ExplicitNativeWeightedPacking
public import RequestProject.TypedTriangle.VortexFixedWindowPositivePacking
public import RequestProject.TypedTriangle.NativeLocalizedSignedPacking
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.WeightedStar.Explicit
open LocalizedCover

def monitoredPackingOrder (C α c η : ℝ) (q : ℕ) : ℕ :=
  max 2 (NativeNibble.Explicit.nativePackingCut C (min c (α/2)) η (q+2))

theorem monitored_sparse_packing_explicit (C α c η : ℝ) (q : ℕ)
    (hC : 0 < C) (hα : 0 < α) (hc : 0 < c) (hη : 0 < η) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), monitoredPackingOrder C α c η q ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      CommonNbrCond H F α → ∀ (κ : Type) [Fintype κ] (W : κ → Finset V → ℝ),
      (Fintype.card κ:ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → 0 ≤ W k T ∧ W k T ≤ 1) →
      (∀ k, c*Fintype.card V ≤ ∑ T ∈ allowed H F, φ T*W k T) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H \ P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        ∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed H F, φ T*W k T)| ≤
          η*(∑ T ∈ allowed H F, φ T*W k T) := by
  let c' := min c (α/2)
  have hc' : 0 < c' := lt_min hc (by positivity)
  let nP := NativeNibble.Explicit.nativePackingCut C c' η (q+2)
  intro V I _ H F φ hn hφ h3 κ _ W hκ hW hmass
  classical
  change max 2 nP ≤ Fintype.card V at hn
  let AV := {v : V // ActiveRoot H F v}
  let W' : (κ ⊕ AV) → Finset V → ℝ := fun k => match k with
    | Sum.inl j => W j
    | Sum.inr v => starWeight v.1
  have hn2 : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast (le_max_left _ _).trans hn
  have hn1 : (1:ℝ) ≤ Fintype.card V := by linarith
  have hn0 : (0:ℝ) ≤ Fintype.card V := by positivity
  have hav : (Fintype.card AV:ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_subtype_le (ActiveRoot H F)
  have hpow1 : (1:ℝ) ≤ (Fintype.card V:ℝ)^q := one_le_pow₀ hn1
  have hpow : (Fintype.card V:ℝ)^q+Fintype.card V ≤ (Fintype.card V:ℝ)^(q+2) := by
    let n := (Fintype.card V:ℝ)
    have hp : 0 ≤ n^q := by positivity
    calc n^q+n ≤ n^q+n^q*n := add_le_add le_rfl (le_mul_of_one_le_left hn0 hpow1)
      _ = n^q*(1+n) := by ring
      _ ≤ n^q*n^2 := mul_le_mul_of_nonneg_left (by dsimp [n]; nlinarith) hp
      _ = n^(q+2) := by rw [pow_add]
  have hcount : (Fintype.card (κ ⊕ AV):ℝ) ≤ (Fintype.card V:ℝ)^(q+2) := by
    rw [Fintype.card_sum,Nat.cast_add]
    exact (add_le_add hκ hav).trans hpow
  have hW' : ∀ k T, IsAllowed H F T → 0 ≤ W' k T ∧ W' k T ≤ 1 := by
    intro k T hT
    cases k with
    | inl j => exact hW j T hT
    | inr v => dsimp [W',starWeight]; split_ifs <;> norm_num
  have hmass' : ∀ k, c'*Fintype.card V ≤ ∑ T ∈ allowed H F, φ T*W' k T := by
    intro k
    cases k with
    | inl j => exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0).trans (hmass j)
    | inr v => exact (mul_le_mul_of_nonneg_right (min_le_right c (α/2)) hn0).trans (seed_star_mass_bounds H F φ hφ h3 v.2).1
  obtain ⟨P,hPsub,hP,hWeights⟩ := NativeNibble.Explicit.weighted_packing_of_diffuse_seed_explicit C c' η (q+2) hC hc' hη H F φ ((le_max_right _ _).trans hn) hφ
    (κ ⊕ AV) W' hcount hW' hmass'
  refine ⟨P,hPsub,hP,sparse_leftover_of_star_tests H F φ hφ hη.le P hP ?_,?_⟩
  · intro v
    by_cases hv : ActiveRoot H F v
    · exact hWeights (Sum.inr ⟨v,hv⟩)
    · have hsel : ∑ T ∈ P, starWeight v T=0 := by
        apply sum_eq_zero
        intro T hT
        apply if_neg
        exact fun hvT => hv ⟨T,hP.1 T hT,hvT⟩
      have hseed : ∑ T ∈ allowed H F, φ T*starWeight v T=0 := by
        apply sum_eq_zero
        intro T hT
        have hh : v ∉ T := fun hvT => hv ⟨T,isAllowed_of_mem_allowed hT,hvT⟩
        simp only [starWeight,if_neg hh,mul_zero]
      rw [hsel,hseed]
      norm_num
  · intro k
    exact hWeights (Sum.inl k)

end TypedTriangle.WeightedStar.Explicit

namespace TypedTriangle.WeightedStar.Explicit
open LocalizedCover

def signedEnvelopeOrder (C α c η τ B : ℝ) (q : ℕ) : ℕ :=
  max 2 (monitoredPackingOrder C α (c/3) (min η (τ/(5*B))) (q+1))

theorem signed_envelope_sparse_packing_explicit (C α c η τ B : ℝ) (q : ℕ)
    (hC : 0 < C) (hα : 0 < α) (hc : 0 < c) (hη : 0 < η) (hτ : 0 < τ) (hB : 0 < B) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), signedEnvelopeOrder C α c η τ B q ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      CommonNbrCond H F α → ∀ (κ : Type) [Fintype κ]
      (A W : κ → Finset V → ℝ),
      (Fintype.card κ:ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → 0 ≤ A k T ∧ A k T ≤ 1 ∧ |W k T| ≤ B*A k T) →
      (∀ k, c*Fintype.card V ≤ ∑ T ∈ allowed H F, φ T*A k T) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        ∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed H F, φ T*W k T)| ≤
          τ*(∑ T ∈ allowed H F, φ T*A k T) := by
  let ε := min η (τ/(5*B))
  have hε : 0 < ε := lt_min hη (by positivity)
  let nP := monitoredPackingOrder C α (c/3) ε (q+1)
  intro V I _ H F φ hn hφ h3 κ _ A W hκ hAW hmass
  change max 2 nP ≤ Fintype.card V at hn
  have hn2 : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast (le_max_left _ _).trans hn
  have hφ0 : ∀ T ∈ allowed H F, 0 ≤ φ T := by
    intro T hT
    exact (by positivity : (0:ℝ) ≤ 1/(C*Fintype.card V)).trans
      (hφ.1 T (isAllowed_of_mem_allowed hT)).1
  let J : κ × Bool → Finset V → ℝ := fun k T =>
    if k.2 then (W k.1 T/B+2*A k.1 T)/3 else A k.1 T/2
  have hJ : ∀ k T, IsAllowed H F T → A k.1 T/3 ≤ J k T ∧ J k T ≤ A k.1 T := by
    intro k T hT
    obtain ⟨hA0,hA1,hW⟩ := hAW k.1 T hT
    have hh := abs_le.mp hW
    have hlo : -A k.1 T ≤ W k.1 T/B :=
      (le_div_iff₀ hB).mpr (by nlinarith only [hh.1])
    have hhi : W k.1 T/B ≤ A k.1 T :=
      (div_le_iff₀ hB).mpr (by nlinarith only [hh.2])
    dsimp [J]
    split_ifs <;> constructor <;> linarith
  have hcount : (Fintype.card (κ × Bool):ℝ) ≤ (Fintype.card V:ℝ)^(q+1) := by
    rw [Fintype.card_prod,show Fintype.card Bool = 2 from rfl,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
    exact mul_le_mul hκ hn2 (by norm_num) (by positivity)
  have hmass' : ∀ k, c/3*Fintype.card V ≤ ∑ T ∈ allowed H F, φ T*J k T := by
    intro k
    have hh := sum_le_sum (s:=allowed H F) (fun T hT =>
      mul_le_mul_of_nonneg_left (hJ k T (isAllowed_of_mem_allowed hT)).1 (hφ0 T hT))
    have hm := hmass k.1
    simp_rw [←mul_div_assoc] at hh
    rw [←sum_div] at hh
    nlinarith only [hh,hm]
  obtain ⟨P,hPsub,hP,hSparse,hTest⟩ := monitored_sparse_packing_explicit C α (c/3) ε (q+1) hC hα (by positivity) hε H F φ ((le_max_right _ _).trans hn) hφ h3
    (κ × Bool) J hcount (fun k T hT => ⟨by linarith [(hJ k T hT).1,(hAW k.1 T hT).1],
      (hJ k T hT).2.trans (hAW k.1 T hT).2.1⟩) hmass'
  let mass := fun k => ∑ T ∈ allowed H F, φ T*A k T
  have htest : ∀ k, |(∑ T ∈ P, J k T)-(∑ T ∈ allowed H F, φ T*J k T)| ≤ ε*mass k.1 := by
    intro k
    exact (hTest k).trans (mul_le_mul_of_nonneg_left (sum_le_sum fun T hT =>
      mul_le_mul_of_nonneg_left (hJ k T (isAllowed_of_mem_allowed hT)).2 (hφ0 T hT)) hε.le)
  refine ⟨P,hPsub,hP,fun v => (hSparse v).trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)),?_⟩
  intro k
  have hpoint : ∀ T, W k T = 3*B*J (k,true) T-4*B*J (k,false) T := by
    intro T
    dsimp [J]
    field_simp
    ring
  have hpacked : (∑ T ∈ P, W k T) =
      3*B*(∑ T ∈ P, J (k,true) T)-4*B*(∑ T ∈ P, J (k,false) T) := by
    simp_rw [hpoint]
    rw [sum_sub_distrib,←mul_sum,←mul_sum]
  have hseed : (∑ T ∈ allowed H F, φ T*W k T) =
      3*B*(∑ T ∈ allowed H F, φ T*J (k,true) T)-4*B*(∑ T ∈ allowed H F, φ T*J (k,false) T) := by
    simp_rw [hpoint]
    simp only [mul_sub]
    rw [sum_sub_distrib]
    congr 1 <;> rw [mul_sum] <;> apply sum_congr rfl <;> intro T _ <;> ring
  have hf := hTest (k,false)
  have hfalse : |(∑ T ∈ P, J (k,false) T)-(∑ T ∈ allowed H F, φ T*J (k,false) T)| ≤
      ε*(mass k/2) := by
    simpa [J,mass,mul_div_assoc,sum_div] using hf
  have htrue := htest (k,true)
  have hM : 0 ≤ mass k := sum_nonneg fun T hT =>
    mul_nonneg (hφ0 T hT) (hAW k T (isAllowed_of_mem_allowed hT)).1
  have hcoef : 5*B*ε ≤ τ := by
    have hh := (le_div_iff₀ (by positivity : 0 < 5*B)).mp (min_le_right η (τ/(5*B)))
    change ε*(5*B) ≤ τ at hh
    nlinarith only [hh]
  rw [hpacked,hseed]
  have hab := abs_sub (3*B*((∑ T ∈ P, J (k,true) T)-(∑ T ∈ allowed H F, φ T*J (k,true) T)))
    (4*B*((∑ T ∈ P, J (k,false) T)-(∑ T ∈ allowed H F, φ T*J (k,false) T)))
  simp only [abs_mul,abs_of_pos hB,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3),
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)] at hab
  have hb := add_le_add (mul_le_mul_of_nonneg_left htrue (by positivity : 0 ≤ 3*B))
    (mul_le_mul_of_nonneg_left hfalse (by positivity : 0 ≤ 4*B))
  have hc' := mul_le_mul_of_nonneg_right hcoef hM
  have hid : 3*B*(∑ T ∈ P, J (k,true) T)-4*B*(∑ T ∈ P, J (k,false) T)-
      (3*B*(∑ T ∈ allowed H F, φ T*J (k,true) T)-4*B*(∑ T ∈ allowed H F, φ T*J (k,false) T)) =
      3*B*((∑ T ∈ P, J (k,true) T)-(∑ T ∈ allowed H F, φ T*J (k,true) T))-
      4*B*((∑ T ∈ P, J (k,false) T)-(∑ T ∈ allowed H F, φ T*J (k,false) T)) := by ring
  rw [hid]
  exact hab.trans (by nlinarith only [hb,hc'])

end TypedTriangle.WeightedStar.Explicit

namespace TypedTriangle.WeightedStar.Explicit
open LocalizedCover

def localizedSignedOrder (C α η τ L : ℝ) (q : ℕ) : ℕ :=
  signedEnvelopeOrder C α (α/6) η (6*τ) (9*L) q

theorem localized_signed_packing_of_H1H3_explicit (C α η τ L : ℝ) (q : ℕ)
    (hC : 0 < C) (hα : 0 < α) (hη : 0 < η) (hτ : 0 < τ) (hL : 0 < L) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), localizedSignedOrder C α η τ L q ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      CommonNbrCond H F α → ∀ (κ : Type) [Fintype κ]
      (bad : κ → Finset V) (W : κ → Finset V → ℝ),
      (Fintype.card κ:ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → |W k T| ≤ 3*L*(T∩bad k).card) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        ∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed H F, φ T*W k T)| ≤
          τ*Fintype.card V*(bad k).card := by
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
  obtain ⟨P,hPsub,hP,hSparse,hQuota⟩ := signed_envelope_sparse_packing_explicit C α (α/6) η (6*τ) (9*L) q hC hα (by positivity) hη (by positivity) (by positivity) H F φ hn hφ h3 AK
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

end TypedTriangle.WeightedStar.Explicit

namespace TypedTriangle.ProtectedNibble.Explicit
open LocalizedCover

def physicalMomentBudget (C α : ℝ) (h : ℕ) : ℝ :=
  min (deletedSeedBudget C α h) (α/4)

def physicalMomentOrder (C α η τ L : ℝ) (h q : ℕ) : ℕ :=
  max (RawReference.Explicit.seedOrder C)
    (WeightedStar.Explicit.localizedSignedOrder (2*C) (α/2) η τ L q)

theorem physicalMomentBudget_pos {C α : ℝ} (h : ℕ) (hC : 1 ≤ C) (hα : 0 < α) :
    0 < physicalMomentBudget C α h :=
  lt_min (deletedSeedBudget_pos h hC hα) (by positivity)

theorem localized_physical_moment_packing_explicit {I : Type} (F : Set (Multiset I))
    (C α η τ L : ℝ) (h q : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η)
    (hτ : 0 < τ) (hL : 0 < L) :
    ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (R : Finset (Sym2 V)) (D : Finset (Finset V)) (d : ℕ),
      physicalMomentOrder C α η τ L h q ≤ Fintype.card V → IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
      CommonNbrCond H F α → HingeCond H F α h → IsDecomposition H F R D →
      (∀ v, degIn R v ≤ d) → (d:ℝ) ≤ physicalMomentBudget C α h*Fintype.card V →
      ∀ (κ : Type) [Fintype κ] (bad : κ → Finset V) (lam : κ → Sym2 V → ℝ),
        (Fintype.card κ:ℝ) ≤ (Fintype.card V:ℝ)^q →
        (∀ k T, IsAllowed H F T → |triSum (lam k) T| ≤ 3*L*(T∩bad k).card) →
        ∃ P : Finset (Finset V), IsPacking H F P ∧ Disjoint (P.biUnion triEdges) R ∧
          IsPhysical H F ((edges H\R)\P.biUnion triEdges) ∧
          (∀ v, (((((edges H\R)\P.biUnion triEdges).filter (fun e => v ∈ e)).card):ℝ) ≤ η*Fintype.card V) ∧
          ∀ k, |edgeSum (lam k) ((edges H\R)\P.biUnion triEdges)| ≤
            τ*Fintype.card V*(bad k).card := by
  let εS := deletedSeedBudget C α h
  let nS := RawReference.Explicit.seedOrder C
  let nP := WeightedStar.Explicit.localizedSignedOrder (2*C) (α/2) η τ L q
  intro V _ H φ R D d hn hφ h2 h3 h4 hD hdeg hd κ _ bad lam hκ htri
  change max nS nP ≤ Fintype.card V at hn
  have hRsub : R ⊆ edges H := by
    rw [←hD.2.2]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hD.1 T hT) heT
  have hn0 : (0:ℝ) ≤ Fintype.card V := by positivity
  have hdS : (d:ℝ) ≤ εS*Fintype.card V :=
    hd.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
  have hd3 : (d:ℝ) ≤ α/4*Fintype.card V :=
    hd.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0)
  have hres3 := residual_commonNbrCond h3 R d hdeg hd3
  obtain ⟨ψ,hψ,-⟩ := seed_persistence_exact_explicit (F:=F) hC hα h H φ R D d ((le_max_left _ _).trans hn) hφ h4 hRsub hD hdeg hdS
  obtain ⟨P,hPsub,hP,hSparse,hQuota⟩ := WeightedStar.Explicit.localized_signed_packing_of_H1H3_explicit (2*C) (α/2) η τ L q (by linarith) (by positivity) hη hτ hL (residual H R) F ψ
    ((le_max_right _ _).trans hn) hψ hres3 κ bad (fun k => triSum (lam k)) hκ
    (fun k T hT => htri k T (isAllowed_mono (subHost_le H _) rfl hT))
  have hPH : IsPacking H F P := ⟨fun T hT =>
    isAllowed_mono (subHost_le H _) rfl (hP.1 T hT),hP.2⟩
  have hJ : edges (residual H R) = edges H\R := Residual.edges_subHost_eq sdiff_subset
  have hPE : P.biUnion triEdges ⊆ edges H\R := by
    rw [←hJ]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  have hDis : Disjoint (P.biUnion triEdges) R :=
    disjoint_left.mpr fun e he hR => (mem_sdiff.mp (hPE he)).2 hR
  have hPhys := isPhysical_sdiff (isPhysical_sdiff_of_decomposition h2 hD hRsub)
    (isPhysical_of_isDecomposition hPH.isDecomposition) hPE
  refine ⟨P,hPH,hDis,hPhys,?_,?_⟩
  · simpa only [hJ] using hSparse
  · intro k
    have hh := remainder_moment_of_quota hψ P hPH (by rw [hJ]; exact hPE) (lam k)
      (τ*Fintype.card V*(bad k).card) (hQuota k)
    simpa only [hJ] using hh

end TypedTriangle.ProtectedNibble.Explicit

namespace TypedTriangle.ProtectedNibble.Explicit
open LocalizedCover



theorem joint_physical_moment_packing_explicit {I : Type} (F : Set (Multiset I))
    (C α η τ L : ℝ) (h q : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η)
    (hτ : 0 < τ) (hL : 0 < L) :
    ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (R : Finset (Sym2 V)) (D : Finset (Finset V)) (d : ℕ),
      physicalMomentOrder C α η τ L h q ≤ Fintype.card V → IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
      CommonNbrCond H F α → HingeCond H F α h → IsDecomposition H F R D →
      (∀ v, degIn R v ≤ d) → (d:ℝ) ≤ physicalMomentBudget C α h*Fintype.card V →
      ∀ (κ ι : Type) [Fintype κ] [Fintype ι]
        (bad : κ → Finset V) (loc : κ → Sym2 V → ℝ) (full : ι → Sym2 V → ℝ),
        ((Fintype.card κ+Fintype.card ι:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^q →
        (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*L*(T∩bad k).card) →
        (∀ j T, IsAllowed H F T → |triSum (full j) T| ≤ 3*L*T.card) →
        ∃ P : Finset (Finset V), IsPacking H F P ∧ Disjoint (P.biUnion triEdges) R ∧
          IsPhysical H F ((edges H\R)\P.biUnion triEdges) ∧
          (∀ v, (((((edges H\R)\P.biUnion triEdges).filter (fun e => v ∈ e)).card):ℝ) ≤ η*Fintype.card V) ∧
          (∀ k, |edgeSum (loc k) ((edges H\R)\P.biUnion triEdges)| ≤
            τ*Fintype.card V*(bad k).card) ∧
          ∀ j, |edgeSum (full j) ((edges H\R)\P.biUnion triEdges)| ≤
            τ*(Fintype.card V:ℝ)^2 := by
  intro V _ H φ R D d hn hφ h2 h3 h4 hD hdeg hd κ ι _ _ bad loc full hcard hloc hfull
  let bad' : κ ⊕ ι → Finset V := Sum.elim bad (fun _ => univ)
  let lam : κ ⊕ ι → Sym2 V → ℝ := Sum.elim loc full
  have hcount : (Fintype.card (κ ⊕ ι):ℝ) ≤ (Fintype.card V:ℝ)^q := by
    simpa only [Fintype.card_sum] using hcard
  have htri : ∀ k T, IsAllowed H F T → |triSum (lam k) T| ≤ 3*L*(T∩bad' k).card := by
    intro k T hT
    cases k with
    | inl k => exact hloc k T hT
    | inr j => simpa [lam,bad'] using hfull j T hT
  obtain ⟨P,hP,hDis,hPhys,hSparse,hQuota⟩ :=
    localized_physical_moment_packing_explicit F C α η τ L h q hC hα hη hτ hL H φ R D d hn hφ h2 h3 h4 hD hdeg hd (κ ⊕ ι) bad' lam hcount htri
  refine ⟨P,hP,hDis,hPhys,hSparse,fun k => hQuota (.inl k),?_⟩
  intro j
  have hh := hQuota (.inr j)
  simpa [lam,bad',pow_two,mul_assoc] using hh

end TypedTriangle.ProtectedNibble.Explicit

namespace TypedTriangle.StockEntry.Explicit
open LocalizedCover

open BasalIncidence ProtectedNibble

def stockMomentOrder (C α κ η τ L : ℝ) (h qMon : ℕ) : ℕ :=
  max (ProtectedNibble.Explicit.physicalMomentOrder C α
      (min (coverDownBudget κ η/4) (1/4)) τ L h qMon)
    (max (coverDownOrder κ η) ⌈2/coverDownBudget κ η⌉₊)

theorem g4_nibble_after_stock_deletion_explicit {I : Type} (F : Set (Multiset I))
    (C α κ η τ L : ℝ) (h qMon : ℕ) (hC : 1 ≤ C) (hα : 0 < α)
    (hκ : 0 < κ) (hη : 0 < η) (hτ : 0 < τ) (hL : 0 < L) :
    ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (D DR : Finset (Finset V)) (R : Finset (Sym2 V)),
        stockMomentOrder C α κ η τ L h qMon ≤ Fintype.card V →
        let S := cover D∪R
        let J := subHost H (edges H\S)
        IsDiffuseSeed J F C φ → IsPhysical J F (edges J) →
        CommonNbrCond J F α → HingeCond J F α h →
        IsPhysical H F (edges H) →
        IsDecomposition H F (cover D) D → IsDecomposition H F R DR →
        Disjoint (cover D) R →
        (∀ u v, H.G.Adj u v → κ*Fintype.card V ≤ (good H F D u v).card) →
        ∀ (κi ι : Type) [Fintype κi] [Fintype ι]
          (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
          (full : ι → Sym2 V → ℝ),
          ((Fintype.card κi+Fintype.card ι:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^qMon →
          (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤
            3*L*(T∩bad k).card) →
          (∀ j T, IsAllowed H F T → |triSum (full j) T| ≤ 3*L*T.card) →
          ∃ Q : Finset (Finset V), IsPacking H F Q ∧
            Disjoint (Q.biUnion triEdges) R ∧
            (edges H\(R∪Q.biUnion triEdges)) ⊆ cover D ∧
            IsPhysical H F (edges H\(R∪Q.biUnion triEdges)) ∧
            ∃ d q : ℕ, ((2*d+2*q:ℕ):ℝ) ≤ η*Fintype.card V ∧
              (∀ k, |edgeSum (loc k) (edges H\(R∪Q.biUnion triEdges))-
                  edgeSum (loc k) (cover D)| ≤
                τ*Fintype.card V*(bad k).card+
                  (3*L*(bad k).card)*(2*d+2*q:ℕ)/2) ∧
              ∀ j, |edgeSum (full j) (edges H\(R∪Q.biUnion triEdges))-
                  edgeSum (full j) (cover D)| ≤
                τ*(Fintype.card V:ℝ)^2+
                  (3*L*Fintype.card V)*(2*d+2*q:ℕ)/2 := by
  let εc := coverDownBudget κ η
  have hεc : 0 < εc := coverDownBudget_pos hκ hη
  let nW := coverDownOrder κ η
  let δ := min (εc/4) (1/4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  let εN := ProtectedNibble.Explicit.physicalMomentBudget C α h
  have hεN := ProtectedNibble.Explicit.physicalMomentBudget_pos h hC hα
  let nP := ProtectedNibble.Explicit.physicalMomentOrder C α δ τ L h qMon
  intro V _ H φ D DR R hn
  change max nP (max nW ⌈2/εc⌉₊) ≤ Fintype.card V at hn
  dsimp only
  intro hSeed hPhysJ h3 h4 hPhysH hD hR hXR hSupply
    κi ι _ _ bad loc full hcount hloc hfull
  let S := cover D∪R
  let J := subHost H (edges H\S)
  have hEmptyDec : IsDecomposition J F ∅ (∅ : Finset (Finset V)) := by
    simp [IsDecomposition]
  have hAllowLoc : ∀ k T, IsAllowed J F T →
      |triSum (loc k) T| ≤ 3*L*(T∩bad k).card := by
    intro k T hT
    exact hloc k T (isAllowed_mono (subHost_le H _) rfl hT)
  have hAllowFull : ∀ j T, IsAllowed J F T →
      |triSum (full j) T| ≤ 3*L*T.card := by
    intro j T hT
    exact hfull j T (isAllowed_mono (subHost_le H _) rfl hT)
  have hnP : nP ≤ Fintype.card V := (le_max_left _ _).trans hn
  obtain ⟨P,hPJ,hPEmpty,hUphys,hSparse,hLocal,hGlobal⟩ :=
    ProtectedNibble.Explicit.joint_physical_moment_packing_explicit F C α δ τ L h qMon hC hα hδ hτ hL J φ ∅ ∅ 0 hnP hSeed hPhysJ h3 h4 hEmptyDec
      (by intro v; simp [degIn])
      (by simpa using (show (0:ℝ) ≤ εN*Fintype.card V from by positivity))
      κi ι bad loc full hcount hAllowLoc hAllowFull
  have hPH : IsPacking H F P :=
    ⟨fun T hT => isAllowed_mono (subHost_le H _) rfl (hPJ.1 T hT),hPJ.2⟩
  have hPE : P.biUnion triEdges ⊆ edges J := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hPJ.1 T hT) heT
  have hPDis : Disjoint (P.biUnion triEdges) S := by
    apply disjoint_left.mpr
    intro e heP heS
    have hh : e ∈ edges H\S := by
      rw [←Residual.edges_subHost_eq (sdiff_subset : edges H\S ⊆ edges H)]
      exact hPE heP
    exact (mem_sdiff.mp hh).2 heS
  let U := edges J\P.biUnion triEdges
  let d := ⌈δ*Fintype.card V⌉₊
  have hdU : ∀ v, (U.filter (fun e => v ∈ e)).card ≤ d := by
    intro v
    have hv : (((edges J\∅)\P.biUnion triEdges).filter
        (fun e => v ∈ e)).card ≤ d := by
      exact_mod_cast (hSparse v).trans (Nat.le_ceil _)
    simpa only [U, sdiff_empty] using hv
  have hnε : 2 ≤ εc*Fintype.card V := by
    have h1 : 2/εc ≤ (Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hn))
    have hh := (div_le_iff₀ hεc).mp h1
    nlinarith
  have hdε : (d:ℝ) ≤ εc*Fintype.card V := by
    have hc : (d:ℝ) < δ*Fintype.card V+1 := Nat.ceil_lt_add_one (by positivity)
    have hδc : δ ≤ εc/4 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hδc (by positivity : (0:ℝ) ≤ Fintype.card V)]
  have hdiag : ∀ e ∈ U, ¬e.IsDiag := by
    intro e he
    have heJ : e ∈ edges J := (mem_sdiff.mp he).1
    have heH : e ∈ edges H := (mem_sdiff.mp (by
      simpa only [J, Residual.edges_subHost_eq sdiff_subset] using heJ :
        e ∈ edges H\S)).1
    exact H.G.not_isDiag_of_mem_edgeSet (by simpa [edges] using heH)
  have hm := Envelope.two_card_le_card_mul_degree U hdiag hdU
  obtain ⟨hwin,hqdeg⟩ := cover_down_window_explicit κ η hκ hη (Fintype.card V) U.card d
    ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
    (by omega) hdε
  let q := coverDownQuota κ η (Fintype.card V)
  have hJE : edges J = edges H\S := Residual.edges_subHost_eq sdiff_subset
  obtain ⟨Q,hQ,hQR,hrem,hQphys,hQl,hQg⟩ :=
    joint_monitored_stock_transition H F D DR P R hD hR hXR hPhysH
      hPH hPDis hSupply d q
      (by simpa only [S,J,U,hJE] using hdU)
      (by simpa only [S,J,U,hJE] using hwin)
      bad loc full L τ τ hL.le hloc hfull
       (by simpa only [S,J,U,hJE,sdiff_empty] using hLocal)
       (by simpa only [S,J,U,hJE,sdiff_empty] using hGlobal)
  exact ⟨Q,hQ,hQR,hrem,hQphys,d,q,hqdeg,hQl,hQg⟩

end TypedTriangle.StockEntry.Explicit

namespace TypedTriangle.CatalogNative.Explicit
open LocalizedCover

open BasalIncidence StockEntry ProtectedNibble

theorem nibble_after_basal_remainder_split_explicit {I : Type}
    (F : Set (Multiset I)) (C α κ η τ L : ℝ) (h qMon : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hκ : 0 < κ)
    (hη : 0 < η) (hτ : 0 < τ) (hL : 0 < L) :
    ∀ {V : Type} [Fintype V] (H : Host V I) (ψ : Finset V → ℝ)
        (D DT : Finset (Finset V))
        (R T Bank E : Finset (Sym2 V)),
        StockEntry.Explicit.stockMomentOrder C α κ η τ L h qMon ≤ Fintype.card V →
        let B := (((cover D ∪ R) ∪ T) ∪ Bank) ∪ E
        let J := subHost H (edges H \ B)
        IsDiffuseSeed J F C ψ → IsPhysical J F (edges J) →
        CommonNbrCond J F α → HingeCond J F α h →
        IsPhysical H F (edges H) →
        IsDecomposition H F (cover D) D →
        Basal H F R → IsDecomposition H F T DT →
        Basal H F Bank → Basal H F E →
        Disjoint (cover D) T →
        Disjoint R (cover D ∪ T) →
        Disjoint Bank ((cover D ∪ R) ∪ T) →
        Disjoint E (((cover D ∪ R) ∪ T) ∪ Bank) →
        (∀ u v, H.G.Adj u v →
          κ * Fintype.card V ≤ (good H F D u v).card) →
        ∀ (κi ι : Type) [Fintype κi] [Fintype ι]
          (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
          (full : ι → Sym2 V → ℝ),
          ((Fintype.card κi + Fintype.card ι : ℕ) : ℝ) ≤
            (Fintype.card V : ℝ) ^ qMon →
          (∀ k A, IsAllowed H F A →
            |triSum (loc k) A| ≤ 3 * L * (A ∩ bad k).card) →
          (∀ j A, IsAllowed H F A →
            |triSum (full j) A| ≤ 3 * L * A.card) →
          ∃ (DR Q : Finset (Finset V)) (Rtail : Finset (Sym2 V)),
            IsDecomposition H F Rtail DR ∧
            Disjoint (cover D) Rtail ∧
            cover D ∪ Rtail = B ∧
            IsPacking H F Q ∧
            Disjoint (Q.biUnion triEdges) Rtail ∧
            (edges H \ (Rtail ∪ Q.biUnion triEdges)) ⊆ cover D ∧
            IsPhysical H F (edges H \ (Rtail ∪ Q.biUnion triEdges)) ∧
            ∃ d q : ℕ, ((2*d + 2*q : ℕ) : ℝ) ≤ η * Fintype.card V ∧
              (∀ k, |edgeSum (loc k)
                  (edges H \ (Rtail ∪ Q.biUnion triEdges)) -
                  edgeSum (loc k) (cover D)| ≤
                τ * Fintype.card V * (bad k).card +
                  (3 * L * (bad k).card) * (2*d + 2*q : ℕ) / 2) ∧
              ∀ j, |edgeSum (full j)
                  (edges H \ (Rtail ∪ Q.biUnion triEdges)) -
                  edgeSum (full j) (cover D)| ≤
                τ * (Fintype.card V : ℝ)^2 +
                  (3 * L * Fintype.card V) * (2*d + 2*q : ℕ) / 2 := by
  intro V _ H ψ D DT R T Bank E hn
  dsimp only
  intro hSeed hPhysJ h3 h4 hPhysH hD hR hT hBank hE
    hDT hRDT hBankDis hEDis hSupply κi ι _ _ bad loc full
    hCount hLoc hFull
  obtain ⟨DR,hDR,hDtail,hEq⟩ :=
    basal_remainder_split D DT R T Bank E hR hT hBank hE
      hDT hRDT hBankDis hEDis
  obtain ⟨Q,hQ,hQR,hRem,hRemPhys,d,q,hLoad,hLocOut,hFullOut⟩ :=
    StockEntry.Explicit.g4_nibble_after_stock_deletion_explicit F C α κ η τ L h qMon hC hα hκ hη hτ hL H ψ D DR (((R ∪ T) ∪ Bank) ∪ E) hn
      (by simpa only [hEq] using hSeed)
      (by simpa only [hEq] using hPhysJ)
      (by simpa only [hEq] using h3)
      (by simpa only [hEq] using h4)
      hPhysH hD hDR hDtail hSupply
      κi ι bad loc full hCount hLoc hFull
  exact ⟨DR,Q,((R ∪ T) ∪ Bank) ∪ E,hDR,hDtail,hEq,
    hQ,hQR,hRem,hRemPhys,d,q,hLoad,hLocOut,hFullOut⟩

end TypedTriangle.CatalogNative.Explicit

namespace TypedTriangle.Vortex.Explicit
open LocalizedCover

open CatalogNative StockEntry BasalIncidence S07V42

def fixedPackingOrder (C α κ η τ Λ : ℝ) (h : ℕ) : ℕ :=
  StockEntry.Explicit.stockMomentOrder C α κ η τ Λ h 1

theorem positive_packing_on_fixed_prepared_window_explicit {I : Type}
    (F : Set (Multiset I)) (C α κ ηPack τ Λ τSel : ℝ) (h t : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hκ : 0 < κ)
    (hη : 0 < ηPack) (hτ : 0 < τ) (hΛ : 0 < Λ)
    (ht : Odd t) (ht3 : 3 ≤ t) :
    ∀ {V : Type} [Fintype V]
      (H : Host V I) (ψ : Finset V → ℝ)
      (W : Finset V) (D DT : Finset (Finset V))
      (R T Bank E : Finset (Sym2 V)),
      fixedPackingOrder C α κ ηPack τ Λ h ≤ Fintype.card V →
      let B := (((cover D ∪ R) ∪ T) ∪ Bank) ∪ E
      let Jhost := subHost H (edges H \ B)
      S07V45.CorePathContract H.G H.lab F W t →
      IsDiffuseSeed Jhost F C ψ → IsPhysical Jhost F (edges Jhost) →
      CommonNbrCond Jhost F α → HingeCond Jhost F α h →
      IsPhysical H F (edges H) →
      IsDecomposition H F (cover D) D →
      Basal H F R → IsDecomposition H F T DT →
      Basal H F Bank → Basal H F E →
      Disjoint (cover D) T →
      Disjoint R (cover D ∪ T) →
      Disjoint Bank ((cover D ∪ R) ∪ T) →
      Disjoint E (((cover D ∪ R) ∪ T) ∪ Bank) →
      (∀ u v, H.G.Adj u v →
        κ * Fintype.card V ≤ (good H F D u v).card) →
      (∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
        ∃ Ps Y : Finset (Sym2 V), R ∪ L = Ps ∪ Y ∧
          Disjoint Ps Y ∧ Basal H F Ps ∧
          (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
          (∀ v, (SelSimul.edeg Y v : ℝ) ≤ τSel * Fintype.card V) ∧
          IsPhysical H F Y) →
      ∀ (κi ι : Type) [Fintype κi] [Fintype ι]
        (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
        (full : ι → Sym2 V → ℝ),
        ((Fintype.card κi + Fintype.card ι : ℕ) : ℝ) ≤
          Fintype.card V →
        (∀ k A, IsAllowed H F A →
          |triSum (loc k) A| ≤ 3 * Λ * (A ∩ bad k).card) →
        (∀ j A, IsAllowed H F A →
          |triSum (full j) A| ≤ 3 * Λ * A.card) →
        ∃ (DR Q : Finset (Finset V))
          (Rtail Ps Y : Finset (Sym2 V))
          (x : MCore H.G H.lab F W) (d q : ℕ),
          IsDecomposition H F Rtail DR ∧
          Disjoint (cover D) Rtail ∧ cover D ∪ Rtail = B ∧
          IsPacking H F Q ∧ Disjoint (Q.biUnion triEdges) Rtail ∧
          (edges H \ (Rtail ∪ Q.biUnion triEdges)) ⊆ cover D ∧
          IsPhysical H F (edges H \ (Rtail ∪ Q.biUnion triEdges)) ∧
          R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) = Ps ∪ Y ∧
          Disjoint Ps Y ∧ Basal H F Ps ∧ IsPhysical H F Y ∧
          (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
          (∀ v, (SelSimul.edeg Y v : ℝ) ≤ τSel * Fintype.card V) ∧
          (x : Sym2 V → ℤ) = SparseEdge.ind Y ∧
          clsQ H.G H.lab F W (x : Sym2 V → ℤ) ∈
            KZ H.G H.lab F W ∅ ∧
          ((2*d+2*q : ℕ) : ℝ) ≤ ηPack * Fintype.card V ∧
          (∀ k, |edgeSum (loc k)
              (edges H \ (Rtail ∪ Q.biUnion triEdges)) -
              edgeSum (loc k) (cover D)| ≤
            τ * Fintype.card V * (bad k).card +
              (3 * Λ * (bad k).card) * (2*d+2*q : ℕ) / 2) ∧
          ∀ j, |edgeSum (full j)
              (edges H \ (Rtail ∪ Q.biUnion triEdges)) -
              edgeSum (full j) (cover D)| ≤
            τ * (Fintype.card V : ℝ)^2 +
              (3 * Λ * Fintype.card V) * (2*d+2*q : ℕ) / 2 := by
  intro V _ H ψ W D DT R T Bank E hn
  dsimp only
  intro hPath hSeed hPhysJ h3 h4 hPhys hD hR hT hBank hE
    hDT hRDT hBankDis hEDis hSupply hMode
    κi ι _ _ bad loc full hCount hLoc hFull
  have hCount' : ((Fintype.card κi + Fintype.card ι : ℕ) : ℝ) ≤
      (Fintype.card V : ℝ)^1 := by simpa using hCount
  obtain ⟨DR,Q,Rtail,hDR,hDtail,hEq,hQ,hQR,hRes,hPhysRes,
    d,q,hLoad,hLocOut,hFullOut⟩ :=
    CatalogNative.Explicit.nibble_after_basal_remainder_split_explicit F C α κ ηPack τ Λ h 1 hC hα hκ hη hτ hΛ H ψ D DT R T Bank E hn hSeed hPhysJ h3 h4 hPhys
      hD hR hT hBank hE hDT hRDT hBankDis hEDis hSupply
      κi ι bad loc full hCount' hLoc hFull
  obtain ⟨Ps,Y,hMove,hPY,hPs,hYin,hYdeg,hYphys⟩ :=
    hMode (edges H \ (Rtail ∪ Q.biUnion triEdges)) hRes hPhysRes
  have hRE : R ⊆ edges H := CorePaid.basal_subset_edges hR
  have hYE : Y ⊆ edges H := by
    intro e heY
    have heRL : e ∈ R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) := by
      rw [hMove]
      exact mem_union_right _ heY
    rcases mem_union.mp heRL with heR | heL
    · exact hRE heR
    · exact (mem_sdiff.mp heL).1
  have hYsub : Y ⊆ SparseEdge.edges (indG H.G W) :=
    g4_positive_payload_in_child H W Y hYE hYin
  obtain ⟨x,hx,hCharge⟩ :=
    actual_physical_residue_charge H F hPath ht ht3 Y hYphys hYsub
  exact ⟨DR,Q,Rtail,Ps,Y,x,d,q,hDR,hDtail,hEq,hQ,hQR,hRes,
    hPhysRes,hMove,hPY,hPs,hYphys,hYin,hYdeg,hx,hCharge,hLoad,
    hLocOut,hFullOut⟩

end TypedTriangle.Vortex.Explicit

#print axioms TypedTriangle.WeightedStar.Explicit.monitored_sparse_packing_explicit
#print axioms TypedTriangle.WeightedStar.Explicit.signed_envelope_sparse_packing_explicit
#print axioms TypedTriangle.WeightedStar.Explicit.localized_signed_packing_of_H1H3_explicit
#print axioms TypedTriangle.ProtectedNibble.Explicit.localized_physical_moment_packing_explicit
#print axioms TypedTriangle.ProtectedNibble.Explicit.joint_physical_moment_packing_explicit
#print axioms TypedTriangle.StockEntry.Explicit.g4_nibble_after_stock_deletion_explicit
#print axioms TypedTriangle.CatalogNative.Explicit.nibble_after_basal_remainder_split_explicit
#print axioms TypedTriangle.Vortex.Explicit.positive_packing_on_fixed_prepared_window_explicit
