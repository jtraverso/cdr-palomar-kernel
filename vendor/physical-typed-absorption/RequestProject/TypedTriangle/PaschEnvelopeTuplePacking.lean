module
public import RequestProject.TypedTriangle.PaschFractionalTuplePacking
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedStar

/-- The actual clone-mass/conditional-degree test used by EGJ. This is a
condition on a chosen tuple test, not a premise on a host in the final theorem. -/
def floorTupleTestControl {V : Type*} [Fintype V] (D : Finset (Finset V))
    (μ : Finset V → ℝ) (P : Finset (Finset V)) (X : Finset (Finset V) → ℝ) (ℓ : ℕ) : Prop :=
  let n := (Fintype.card V:ℝ)
  let p := n^2
  let m := floorCopies D μ n
  (∀ j, 1 ≤ j → j ≤ ℓ → ∀ R : Finset D, R.card = j →
    WeightedClone.tupleExtensionMass (indexedPackets D) m (indexedTupleWeight D X) ℓ R*
      p^((j:ℝ)+1/4) ≤ WeightedClone.tupleMass (indexedPackets D) m (indexedTupleWeight D X) ℓ) →
  |PatternStatistics.statistic X ℓ P-WeightedClone.tupleMass (indexedPackets D) m (indexedTupleWeight D X) ℓ/p^ℓ| ≤
    p^(-egj13Epsilon)*(WeightedClone.tupleMass (indexedPackets D) m (indexedTupleWeight D X) ℓ/p^ℓ)

/-- Signed tests with their OWN nonnegative envelope retain a relative error
at the envelope mass scale. The shift is localized, not a global constant;
one packing controls all envelopes, signed tests, leftover degrees and the
unoriented Pasch count. Every extra eligible tuple test is retained on that
same packing. The Pasch precision is independent of the linear precision. -/
theorem signed_envelope_packing_with_pasch_and_tuple_tests (C α c η τ B σ : ℝ) (q : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hc : 0 < c) (hη : 0 < η) (hτ : 0 < τ) (hB : 0 < B) (hσ : 0 < σ) :
    ∃ n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      CommonNbrCond H F α → ∀ (κ : Type) [Fintype κ]
      (A W : κ → Finset V → ℝ),
      (Fintype.card κ:ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → 0 ≤ A k T ∧ A k T ≤ 1 ∧ |W k T| ≤ B*A k T) →
      (∀ k, c*Fintype.card V ≤ ∑ T ∈ allowed H F, φ T*A k T) →
      ∀ (ν : Type) [Fintype ν] (X : ℕ → ν → Finset (Finset V) → ℝ),
      Fintype.card ν ≤ (Fintype.card V)^q →
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ X ℓ k S) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        (∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed H F, φ T*W k T)| ≤
          τ*(∑ T ∈ allowed H F, φ T*A k T)) ∧
        |(count P:ℝ)-target φ (allowed H F)| ≤ σ*(Fintype.card V:ℝ)^2 ∧
        ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k : ν,
          floorTupleTestControl (allowed H F) φ P (X ℓ k) ℓ := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let ε := min (min η (τ/(5*B))) σ
  have hε : 0 < ε := lt_min (lt_min hη (by positivity)) hσ
  have hεη : ε ≤ η := (min_le_left _ _).trans (min_le_left _ _)
  have hετ : ε ≤ τ/(5*B) := (min_le_left _ _).trans (min_le_right _ _)
  have hεσ : ε ≤ σ := min_le_right _ _
  obtain ⟨nP,hPack⟩ := fractional_packing_with_pasch_and_tuple_tests α C (c/3) ε (q+1) hα hC (by positivity) hε
  refine ⟨max 2 nP,?_⟩
  intro V I _ H F φ hn hφ h3 κ _ A W hκ hAW hmass ν _ X hν hX
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
  have hcountNat : Fintype.card (κ × Bool) ≤ (Fintype.card V)^(q+1) := by exact_mod_cast hcount
  have hν' : Fintype.card ν ≤ (Fintype.card V)^(q+1) :=
    hν.trans (pow_le_pow_right₀ (show 1 ≤ Fintype.card V by exact_mod_cast (show (1:ℝ) ≤ Fintype.card V by linarith only [hn2])) (Nat.le_succ q))
  obtain ⟨P,hPsub,hP,hSparse,hTest,hPasch,hExtra⟩ := hPack H F φ ((le_max_right _ _).trans hn) hφ h3
    (κ × Bool) J hcountNat (fun k T hT => ⟨by linarith [(hJ k T hT).1,(hAW k.1 T hT).1],
      (hJ k T hT).2.trans (hAW k.1 T hT).2.1⟩) hmass' ν X hν' hX
  let mass := fun k => ∑ T ∈ allowed H F, φ T*A k T
  have htest : ∀ k, |(∑ T ∈ P, J k T)-(∑ T ∈ allowed H F, φ T*J k T)| ≤ ε*mass k.1 := by
    intro k
    exact (hTest k).trans (mul_le_mul_of_nonneg_left (sum_le_sum fun T hT =>
      mul_le_mul_of_nonneg_left (hJ k T (isAllowed_of_mem_allowed hT)).2 (hφ0 T hT)) hε.le)
  refine ⟨P,hPsub,hP,fun v => (hSparse v).trans
    (mul_le_mul_of_nonneg_right hεη (by positivity)),?_,
    hPasch.trans (mul_le_mul_of_nonneg_right hεσ (sq_nonneg _)),
    (by intro ℓ hℓ hℓ4 k; exact hExtra ℓ hℓ hℓ4 k)⟩
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
    have hh := (le_div_iff₀ (by positivity : 0 < 5*B)).mp hετ
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

#print axioms signed_envelope_packing_with_pasch_and_tuple_tests
end TypedTriangle.Pasch
