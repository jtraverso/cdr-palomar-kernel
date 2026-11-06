module
public import RequestProject.TypedTriangle.PaschPackingModel
public import RequestProject.TypedTriangle.ClonedTupleIndexedWeights
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedClone WeightedStar

abbrev ExtendedPackingMonitor (V κ ν : Type*) := PackingMonitor V κ ⊕ ν

def extendedPackingTupleWeight {V κ ν : Type*} [Fintype V]
    (D : Finset (Finset V)) (W : κ → Finset V → ℝ)
    (X : ℕ → ν → Finset (Finset V) → ℝ) (ℓ : ℕ) :
    ExtendedPackingMonitor V κ ν → Finset D → ℝ :=
  Sum.elim (packingTupleWeight D W ℓ) (fun k => indexedTupleWeight D (X ℓ k))

theorem extendedPackingMonitor_card_le {V κ ν : Type*} [Fintype V] [Fintype κ] [Fintype ν]
    (q : ℕ) (hn : 2 ≤ Fintype.card V)
    (hκ : Fintype.card κ ≤ (Fintype.card V)^q) (hν : Fintype.card ν ≤ (Fintype.card V)^q) :
    Fintype.card (ExtendedPackingMonitor V κ ν) ≤ (Fintype.card V)^(q+4) := by
  let n := Fintype.card V
  have hn1 : 1 ≤ n := by omega
  have hν' : Fintype.card ν ≤ n^(q+3) := hν.trans (pow_le_pow_right₀ hn1 (by omega))
  calc
    Fintype.card (ExtendedPackingMonitor V κ ν) = Fintype.card (PackingMonitor V κ)+Fintype.card ν := Fintype.card_sum
    _ ≤ n^(q+3)+n^(q+3) := add_le_add (packingMonitor_card_le q hn hκ) hν'
    _ = 2*n^(q+3) := by omega
    _ ≤ n*n^(q+3) := Nat.mul_le_mul_right _ hn
    _ = n^(q+4) := by rw [←pow_succ']

/-- One real packing retains the diffuse-seed/Pasch guarantees and controls
an arbitrary extra family of nonnegative tuple tests whenever the TEST itself
satisfies the displayed actual-clone eligibility inequalities. This is an
intermediate EGJ engine: final applications must discharge those inequalities. -/
theorem fractional_packing_with_pasch_and_tuple_tests (α C c η : ℝ) (q : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hc : 0 < c) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (μ : Finset V → ℝ), N ≤ Fintype.card V → IsDiffuseSeed H F C μ →
      CommonNbrCond H F α → ∀ (κ : Type) [Fintype κ] (W : κ → Finset V → ℝ),
      Fintype.card κ ≤ (Fintype.card V)^q →
      (∀ k T, IsAllowed H F T → 0 ≤ W k T ∧ W k T ≤ 1) →
      (∀ k, c*Fintype.card V ≤ ∑ T ∈ allowed H F, μ T*W k T) →
      ∀ (ν : Type) [Fintype ν] (X : ℕ → ν → Finset (Finset V) → ℝ),
      Fintype.card ν ≤ (Fintype.card V)^q →
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ X ℓ k S) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H \ P.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ) ≤ η*Fintype.card V) ∧
        (∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed H F, μ T*W k T)| ≤
          η*(∑ T ∈ allowed H F, μ T*W k T)) ∧
        |(count P : ℝ)-target μ (allowed H F)| ≤ η*(Fintype.card V : ℝ)^2 ∧
        ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k : ν,
          let A := allowed H F
          let n := (Fintype.card V:ℝ)
          let p := n^2
          let m := floorCopies A μ n
          (∀ j, 1 ≤ j → j ≤ ℓ → ∀ R : Finset A, R.card = j →
            WeightedClone.tupleExtensionMass (indexedPackets A) m (indexedTupleWeight A (X ℓ k)) ℓ R*
              p^((j:ℝ)+1/4) ≤ WeightedClone.tupleMass (indexedPackets A) m (indexedTupleWeight A (X ℓ k)) ℓ) →
          |PatternStatistics.statistic (X ℓ k) ℓ P-
              WeightedClone.tupleMass (indexedPackets A) m (indexedTupleWeight A (X ℓ k)) ℓ/p^ℓ| ≤
            p^(-egj13Epsilon)*(WeightedClone.tupleMass (indexedPackets A) m (indexedTupleWeight A (X ℓ k)) ℓ/p^ℓ) := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let ε := η/(4*C^3)
  let d := min c (α/2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hd : 0 < d := lt_min hc (by positivity)
  have hcp : 0 < massConstant α C := by unfold massConstant; positivity
  obtain ⟨D0,hEGJ⟩ := tuple_matching_from_integer_multiplicities (1/4) (by norm_num) (by norm_num)
    3 (by decide) 4 (by decide)
  obtain ⟨Nnum,hNnum1,hNum⟩ := exists_egj13_square_order C (massConstant α C) ε D0 (q+4) hcp hε
  let N := max (floorEligibilityOrder α C) (max Nnum (max 2 ⌈4/d^2⌉₊))
  refine ⟨N,?_⟩
  intro V I _ H F μ hN hH1 hH3 κ _ W hκ hW hQuota ν _ X hν hX
  let A := allowed H F
  let n := (Fintype.card V : ℝ)
  let p := n^2
  let P0 := indexedPackets A
  let φ : A → ℝ := fun i => μ i.val
  let m := floorCopies A μ n
  have hNE : floorEligibilityOrder α C ≤ Fintype.card V := by dsimp [N] at hN; omega
  have hNN : Nnum ≤ Fintype.card V := by dsimp [N] at hN; omega
  have hn2 : 2 ≤ Fintype.card V := by dsimp [N] at hN; omega
  have hnNat : 0 < Fintype.card V := by omega
  have hn0 : 0 < n := by dsimp only [n]; exact_mod_cast hnNat
  have hNS : ⌈4/d^2⌉₊ ≤ Fintype.card V := by dsimp [N] at hN; omega
  have hSqrt : Real.sqrt n ≤ d*n/2 := sqrt_le_linear_of_order hd hn0 (Nat.ceil_le.mp hNS)
  obtain ⟨hp1,hD0,hCodeNum,hSizeNum,hFamilyNum,hErrorNum,hRound,hScale,hRatio⟩ := hNum (Fintype.card V) hNN
  have hp0 : 0 < p := sq_pos_of_pos hn0
  have hρ0 : 0 ≤ p^(-egj13Epsilon) := Real.rpow_nonneg hp0.le _
  have hSmall : 2*ε ≤ η := by
    have hC3 : 1 ≤ C^3 := one_le_pow₀ hC
    have hden : (2:ℝ) ≤ 4*C^3 := by nlinarith only [hC3]
    have hh := div_le_div_of_nonneg_left hη.le (by norm_num : (0:ℝ) < 2) hden
    change ε ≤ η/2 at hh
    linarith only [hh]
  have hPhi (i : A) : 1/(C*n) ≤ φ i ∧ φ i ≤ C/n := hH1.1 i.val (isAllowed_of_mem_allowed i.property)
  have hPhi0 (i : A) : 0 ≤ φ i := (by positivity : (0:ℝ) ≤ 1/(C*n)).trans (hPhi i).1
  have hCard : ∀ i : A, (P0 i).card = 3 := indexedPackets_uniform A
    (fun T hT => (isAllowed_of_mem_allowed hT).1)
  have hNonempty (i : A) : (P0 i).Nonempty := card_pos.mp (by rw [hCard]; decide)
  have hLoad (e : Sym2 V) : (∑ i : A, if e ∈ P0 i then φ i else 0) ≤ 1 := indexed_load_le_of_seed hH1 e
  have hDeg := floorMultiplicity_degree_cap P0 φ p hp0.le hPhi0 (fun e => by
    convert hLoad e using 1 <;> (apply sum_congr rfl; intro i _; split_ifs <;> rfl))
  have hCode := floorMultiplicity_codegree_cap P0 φ p (C/n) hp0.le (by positivity) hPhi0
    (fun i => (hPhi i).2) (fun e f hef => by
      convert indexed_packets_linear A (fun T hT => (isAllowed_of_mem_allowed hT).1) e f hef using 1
      congr 1
      ext i
      simp only [mem_filter,mem_univ,true_and]
      rfl)
  have hTotal := floorMultiplicity_total_cap P0 φ p hp0.le hPhi0 hNonempty (fun e => by
    convert hLoad e using 1 <;> (apply sum_congr rfl; intro i _; split_ifs <;> rfl))
  have hEcard : (Fintype.card (Sym2 V) : ℝ) ≤ n^2 := by
    dsimp only [n]
    exact_mod_cast (sym2_card_le_square (V:=V))
  have hVol : ((∑ i, m i : ℕ) : ℝ) ≤ n^4 := by
    have hh := hTotal.trans (mul_le_mul_of_nonneg_left hEcard hp0.le)
    exact hh.trans_eq (by dsimp [p]; ring)
  letI : ∀ _ℓ : ℕ, Fintype (ExtendedPackingMonitor V κ ν) := fun _ => inferInstance
  have hFamily : (Fintype.card (ExtendedPackingMonitor V κ ν) : ℝ) ≤ n^(q+4) := by
    dsimp only [n]
    exact_mod_cast extendedPackingMonitor_card_le q hn2 hκ hν
  obtain ⟨CC,hDis,hStatsAll⟩ := hEGJ p hD0 hp1 (Sym2 V) A P0 m hCard
    (fun e => hDeg e) (by
      intro e f hef
      have hh := hCode e f hef
      have he : p*(C/n) = C*n := by dsimp [p]; field_simp [ne_of_gt hn0] <;> ring
      rw [he] at hh
      convert hh.trans hCodeNum using 1 <;> norm_num [p,n,m,floorCopies,φ])
    (by convert hVol.trans hSizeNum using 1 <;> norm_num [egj13Epsilon,p,n])
    (fun _ => ExtendedPackingMonitor V κ ν) (extendedPackingTupleWeight A W X)
    (by
      intro ℓ hℓ hℓ4 k S
      rcases k with k | k
      · exact packingTupleWeight_nonneg A W
          (fun k T hT => (hW k T (isAllowed_of_mem_allowed hT)).1) ℓ k S
      · exact hX ℓ hℓ hℓ4 k (indexProjection A S))
    (by intro ℓ _ _; convert hFamily.trans hFamilyNum using 1 <;> norm_num [egj13Epsilon,p,n])
  have hStats (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓ4 : ℓ ≤ 4) (k : PackingMonitor V κ) :=
    hStatsAll ℓ hℓ hℓ4 (Sum.inl k)
  dsimp only [extendedPackingTupleWeight,Sum.elim_inl] at hStats
  let Q := copyProjection m CC
  let P := indexProjection A Q
  have hPsub : P ⊆ allowed H F := indexProjection_subset A Q
  have hPpack : IsPacking H F P := packing_of_index_matching (baseMatching_of_copyMatching P0 m hDis)
  have hSum (f : Finset V → ℝ) : (∑ T ∈ P, f T) = ∑ i ∈ Q, f i.val := by
    dsimp only [P,indexProjection]
    rw [sum_image]
    intro i _ j _ h
    exact Subtype.ext h
  have hLinear (k : PackingMonitor V κ) (a : A → ℝ)
      (hk : packingTupleWeight A W 1 k = linearTupleWeight a)
      (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
      (hMass : (∑ i, φ i*a i) = 0 ∨ d*n ≤ ∑ i, φ i*a i) :
      |(∑ i ∈ Q, a i)-(∑ i, φ i*a i)| ≤ η*(∑ i, φ i*a i) := by
    have hh := hStats 1 (by decide) (by decide) k (by
      intro j hj hj1 R hRc
      have hjEq : j = 1 := by omega
      have hRc1 : R.card = 1 := hRc.trans hjEq
      obtain ⟨i,hRi⟩ := card_eq_one.mp hRc1
      rw [hjEq,hRi,hk,tupleExtensionMass_linear_singleton]
      simpa only [Nat.cast_one,m,floorCopies,p,φ] using
        floor_linear_eligible P0 hC0 hn0 hRound hSqrt φ a (fun i => (hPhi i).1) ha hMass i)
    rw [hk,statistic_linear] at hh
    simp only [pow_one] at hh
    rw [← normalizedLinearMass_actual P0 m p a] at hh
    have hTest : |(∑ i ∈ Q, a i)-normalizedLinearMass m p a| ≤
        p^(-egj13Epsilon)*normalizedLinearMass m p a := by
      convert hh using 1 <;> norm_num [egj13Epsilon]
    have hh' := linear_floor_test_error hC0 hn0 hε.le hρ0 hErrorNum hRatio φ a
      (fun i => (hPhi i).1) (fun i => (ha i).1) Q hTest
    exact hh'.trans (mul_le_mul_of_nonneg_right hSmall
      (sum_nonneg (fun i _ => mul_nonneg (hPhi0 i) (ha i).1)))
  have hStars : ∀ v, |(∑ T ∈ P, starWeight v T)-(∑ T ∈ allowed H F, μ T*starWeight v T)| ≤
      η*(∑ T ∈ allowed H F, μ T*starWeight v T) := by
    intro v
    have hs : (∑ i : A, φ i*starWeight v i.val) = ∑ T ∈ allowed H F, μ T*starWeight v T :=
      sum_coe_sort A (fun T => μ T*starWeight v T)
    have hMass : (∑ i : A, φ i*starWeight v i.val) = 0 ∨
        d*n ≤ ∑ i : A, φ i*starWeight v i.val := by
      rcases star_seed_mass_zero_or_lower hH1 hH3 v with hz | hl
      · exact Or.inl (hs.trans hz)
      · exact Or.inr ((mul_le_mul_of_nonneg_right (min_le_right c (α/2)) hn0.le).trans (hl.trans_eq hs.symm))
    have hh := hLinear (Sum.inl v) (fun i => starWeight v i.val) (packingTupleWeight_star A W v)
      (fun i => by unfold starWeight; split_ifs <;> norm_num) hMass
    rw [hSum,← hs]
    exact hh
  have hTests : ∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed H F, μ T*W k T)| ≤
      η*(∑ T ∈ allowed H F, μ T*W k T) := by
    intro k
    have hs : (∑ i : A, φ i*W k i.val) = ∑ T ∈ allowed H F, μ T*W k T :=
      sum_coe_sort A (fun T => μ T*W k T)
    have hMass : (∑ i : A, φ i*W k i.val) = 0 ∨ d*n ≤ ∑ i : A, φ i*W k i.val :=
      Or.inr ((mul_le_mul_of_nonneg_right (min_le_left c (α/2)) hn0.le).trans ((hQuota k).trans_eq hs.symm))
    have hh := hLinear (Sum.inr (Sum.inl k)) (fun i => W k i.val) (packingTupleWeight_test A W k)
      (fun i => hW k i.val (isAllowed_of_mem_allowed i.property)) hMass
    rw [hSum,← hs]
    exact hh
  have hPaschRaw := hStats 4 (by decide) (by decide) (Sum.inr (Sum.inr ())) (by
    intro j hj hj4 R hRc
    rw [packingTupleWeight_pasch]
    have hh := floor_paschtuple_eligible hH1 hH3 hα hC hNE R (by omega) (by omega)
    simpa only [hRc] using hh)
  rw [packingTupleWeight_pasch,indexed_statistic_eq_count,tupleMass_indexed_div] at hPaschRaw
  let ψ := floorWeights A μ n
  have hPasch : |(count P : ℝ)-target ψ A| ≤ p^(-egj13Epsilon)*target ψ A := by
    convert hPaschRaw using 1 <;> norm_num [egj13Epsilon,ψ,floorWeights,P,Q,m,p]
  have hLow : ∀ T ∈ A, 1/(C*n) ≤ μ T := fun T hT => (hH1.1 T (isAllowed_of_mem_allowed hT)).1
  have hMu0 : ∀ T ∈ A, 0 ≤ μ T := fun T hT => (by positivity : (0:ℝ) ≤ 1/(C*n)).trans (hLow T hT)
  have ht0 := target_nonneg_on A μ hMu0
  have htψ0 := target_nonneg_on A ψ (fun T _ => floorWeights_nonneg A μ n T)
  have hMono : target ψ A ≤ target μ A := by
    have hh := target_multiplicative_lower A ψ μ 1 (by norm_num)
      (fun T _ => floorWeights_nonneg A μ n T)
      (fun T hT => by simpa only [one_mul] using (floorWeights_bounds A μ hC0 hn0 hLow hT).2)
    simpa only [one_pow,one_mul] using hh
  have hν1 : C/n ≤ 1 := (div_le_one hn0).mpr (by linarith only [hRound,hC0])
  have hBias := target_difference_of_relative_pointwise A μ ψ (C/n) (by positivity) hν1 hMu0 (by
    intro T hT
    have hb := floorWeights_bounds A μ hC0 hn0 hLow hT
    rw [abs_of_nonpos (sub_nonpos.mpr hb.2)]
    linarith only [hb.1])
  have hMatchBound : p^(-egj13Epsilon)*target ψ A ≤ ε*target μ A := mul_le_mul hErrorNum hMono htψ0 hε.le
  have hBiasBound : 15*(C/n)*target μ A ≤ 15*ε*target μ A :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRatio (by norm_num)) ht0
  have hUpper := target_le_seed_order_square hC0 hH1 hnNat
  have hPaschFinal : |(count P : ℝ)-target μ A| ≤ η*n^2 := by
    calc
      _ ≤ |(count P : ℝ)-target ψ A|+|target ψ A-target μ A| := abs_sub_le _ _ _
      _ ≤ ε*target μ A+15*ε*target μ A := add_le_add (hPasch.trans hMatchBound) (hBias.trans hBiasBound)
      _ = 16*ε*target μ A := by ring
      _ ≤ 16*ε*(C^3*n^2/4) := mul_le_mul_of_nonneg_left hUpper (by positivity)
      _ = η*n^2 := by dsimp [ε]; field_simp [ne_of_gt hC0]; ring
  refine ⟨P,hPsub,hPpack,sparse_leftover_of_star_tests H F μ hH1 hη.le P hPpack hStars,hTests,hPaschFinal,?_⟩
  intro ℓ hℓ hℓ4 k
  dsimp only
  intro hEligible
  have hh := hStatsAll ℓ hℓ hℓ4 (Sum.inr k) (by
    simpa only [extendedPackingTupleWeight,Sum.elim_inr] using hEligible)
  dsimp only [extendedPackingTupleWeight,Sum.elim_inr] at hh
  rw [statistic_indexedTupleWeight] at hh
  convert hh using 1 <;> norm_num [egj13Epsilon,P,Q,p,n,m,A,P0]

#print axioms extendedPackingMonitor_card_le
#print axioms fractional_packing_with_pasch_and_tuple_tests
end TypedTriangle.Pasch
