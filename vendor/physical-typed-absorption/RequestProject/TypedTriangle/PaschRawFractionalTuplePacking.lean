module
public import RequestProject.TypedTriangle.PaschRawProfileBounds
public import RequestProject.TypedTriangle.PaschFractionalTuplePacking
public import RequestProject.TypedTriangle.PaschEnvelopeTuplePacking
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

/-- A raw approximate-load packing with arbitrary nonnegative tuple tests.
All tests share the same packing as the sparse remainder and quadratic
Pasch bound. Actual clone eligibility is a condition on each test; it is
not an exact-seed or physicality premise on the host. -/
theorem raw_fractional_packing_with_pasch_and_tuple_tests (a b α η : ℝ) (q : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ) (ε : ℝ), N ≤ Fintype.card V → 0 ≤ ε → ε ≤ 1/2 →
      (∀ T, IsAllowed H F T → a/Fintype.card V ≤ φ T ∧ φ T ≤ b/Fintype.card V) →
      (∀ e ∈ edges H, |bdry H F φ e-1| ≤ ε) → CommonNbrCond H F α →
      ∀ (ν : Type) [Fintype ν] (X : ℕ → ν → Finset (Finset V) → ℝ),
      Fintype.card ν ≤ (Fintype.card V)^q →
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ X ℓ k S) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤
          (2*ε+η)*Fintype.card V) ∧
        (count P:ℝ) ≤ rawPaschPackingCost a b*(Fintype.card V:ℝ)^2 ∧
        ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k : ν,
          floorTupleTestControl (allowed H F) (fun T => φ T/(1+ε)) P (X ℓ k) ℓ := by
  let C := rawProfileConstant a b
  have hC : 1 ≤ C := rawProfileConstant_one_le a b
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let τ := min (η/2) 1
  have hτ : 0 < τ := lt_min (by positivity) zero_lt_one
  let d := α/6
  have hd : 0 < d := by dsimp [d]; positivity
  have hcp : 0 < massConstant α C := by unfold massConstant; positivity
  obtain ⟨D0,hEGJ⟩ := tuple_matching_from_integer_multiplicities (1/4) (by norm_num) (by norm_num)
    3 (by decide) 4 (by decide)
  obtain ⟨Nnum,hNnum1,hNum⟩ := exists_egj13_square_order C (massConstant α C) τ D0 (q+4) hcp hτ
  let N := max (floorEligibilityOrder α C) (max Nnum (max 2 ⌈4/d^2⌉₊))
  refine ⟨N,?_⟩
  intro V I _ H F φ ε hN hε hεHalf hWindow hLoad h3 ν _ X hν hX
  let A := allowed H F
  let n := (Fintype.card V:ℝ)
  let p := n^2
  let μ : Finset V → ℝ := fun T => φ T/(1+ε)
  let P0 := indexedPackets A
  let w : A → ℝ := fun i => μ i.val
  let m := floorCopies A μ n
  let W : Empty → Finset V → ℝ := fun k => nomatch k
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
  have hSmall : 2*τ ≤ η := by
    have hh : τ ≤ η/2 := min_le_left _ _
    linarith only [hh]
  have hρ1 : p^(-egj13Epsilon) ≤ 1 := hErrorNum.trans (min_le_right _ _)
  have hMu (T : Finset V) (hT : T ∈ A) : 1/(C*n) ≤ μ T ∧ μ T ≤ C/n :=
    raw_normalized_coefficient_window ha hε hεHalf hn0 (hWindow T (isAllowed_of_mem_allowed hT))
  have hMu0 (T : Finset V) (hT : T ∈ A) : 0 ≤ μ T :=
    (by positivity : (0:ℝ) ≤ 1/(C*n)).trans (hMu T hT).1
  have hMuLoad (e : Sym2 V) (he : e ∈ edges H) :
      1-2*ε ≤ bdry H F μ e ∧ 1/3 ≤ bdry H F μ e ∧ bdry H F μ e ≤ 1 := by
    rw [bdry_div_constant]
    exact raw_normalized_load_window hε hεHalf (hLoad e he)
  have hPhi (i : A) : 1/(C*n) ≤ w i ∧ w i ≤ C/n := hMu i.val i.property
  have hPhi0 (i : A) : 0 ≤ w i := hMu0 i.val i.property
  have hCard : ∀ i : A, (P0 i).card = 3 := indexedPackets_uniform A
    (fun T hT => (isAllowed_of_mem_allowed hT).1)
  have hNonempty (i : A) : (P0 i).Nonempty := card_pos.mp (by rw [hCard]; decide)
  have hLoadAll (e : Sym2 V) : (∑ i : A, if e ∈ P0 i then w i else 0) ≤ 1 := by
    change (∑ i : allowed H F, if e ∈ indexedPackets (allowed H F) i then μ i.val else 0) ≤ 1
    rw [indexed_load_eq_bdry]
    by_cases he : e ∈ edges H
    · exact (hMuLoad e he).2.2
    · rw [bdry_eq_zero_of_not_mem H F μ he]
      norm_num
  have hDeg := floorMultiplicity_degree_cap P0 w p hp0.le hPhi0 (fun e => by
    convert hLoadAll e using 1 <;> (apply sum_congr rfl; intro i _; split_ifs <;> rfl))
  have hCode := floorMultiplicity_codegree_cap P0 w p (C/n) hp0.le (by positivity) hPhi0
    (fun i => (hPhi i).2) (fun e f hef => by
      convert indexed_packets_linear A (fun T hT => (isAllowed_of_mem_allowed hT).1) e f hef using 1
      congr 1
      ext i
      simp only [mem_filter,mem_univ,true_and]
      rfl)
  have hTotal := floorMultiplicity_total_cap P0 w p hp0.le hPhi0 hNonempty (fun e => by
    convert hLoadAll e using 1 <;> (apply sum_congr rfl; intro i _; split_ifs <;> rfl))
  have hEcard : (Fintype.card (Sym2 V):ℝ) ≤ n^2 := by
    dsimp only [n]
    exact_mod_cast (sym2_card_le_square (V:=V))
  have hVol : ((∑ i, m i : ℕ):ℝ) ≤ n^4 := by
    have hh := hTotal.trans (mul_le_mul_of_nonneg_left hEcard hp0.le)
    exact hh.trans_eq (by dsimp [p]; ring)
  letI : ∀ _ℓ : ℕ, Fintype (ExtendedPackingMonitor V Empty ν) := fun _ => inferInstance
  have hFamily : (Fintype.card (ExtendedPackingMonitor V Empty ν):ℝ) ≤ n^(q+4) := by
    dsimp only [n]
    exact_mod_cast extendedPackingMonitor_card_le q hn2
      (by simp : Fintype.card Empty ≤ (Fintype.card V)^q) hν
  obtain ⟨CC,hDis,hStatsAll⟩ := hEGJ p hD0 hp1 (Sym2 V) A P0 m hCard
    (fun e => hDeg e) (by
      intro e f hef
      have hh := hCode e f hef
      have he : p*(C/n) = C*n := by dsimp [p]; field_simp [ne_of_gt hn0] <;> ring
      rw [he] at hh
      convert hh.trans hCodeNum using 1 <;> norm_num [p,n,m,floorCopies,w])
    (by convert hVol.trans hSizeNum using 1 <;> norm_num [egj13Epsilon,p,n])
    (fun _ => ExtendedPackingMonitor V Empty ν) (extendedPackingTupleWeight A W X)
    (by
      intro ℓ hℓ hℓ4 k S
      rcases k with k | k
      · exact packingTupleWeight_nonneg A W (fun k => nomatch k) ℓ k S
      · exact hX ℓ hℓ hℓ4 k (indexProjection A S))
    (by intro ℓ _ _; convert hFamily.trans hFamilyNum using 1 <;> norm_num [egj13Epsilon,p,n])
  have hStats (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓ4 : ℓ ≤ 4) (k : PackingMonitor V Empty) :=
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
  have hStars : ∀ v, |(∑ T ∈ P, starWeight v T)-(∑ T ∈ allowed H F, μ T*starWeight v T)| ≤
      η*(∑ T ∈ allowed H F, μ T*starWeight v T) := by
    intro v
    let aStar : A → ℝ := fun i => starWeight v i.val
    have haStar (i : A) : 0 ≤ aStar i ∧ aStar i ≤ 1 := by
      dsimp [aStar,starWeight]
      split_ifs <;> norm_num
    have hs : (∑ i : A, w i*aStar i) = ∑ T ∈ allowed H F, μ T*starWeight v T :=
      sum_coe_sort A (fun T => μ T*starWeight v T)
    have hMass : (∑ i : A, w i*aStar i) = 0 ∨ d*n ≤ ∑ i : A, w i*aStar i := by
      rcases raw_star_zero_or_lower h3 (fun e he => (hMuLoad e he).2) v with hz | hl
      · exact Or.inl (hs.trans hz)
      · exact Or.inr (hl.trans_eq hs.symm)
    have hh := hStats 1 (by decide) (by decide) (Sum.inl v) (by
      intro j hj hj1 R hRc
      have hjEq : j = 1 := by omega
      have hRc1 : R.card = 1 := hRc.trans hjEq
      obtain ⟨i,hRi⟩ := card_eq_one.mp hRc1
      rw [hjEq,hRi,packingTupleWeight_star,tupleExtensionMass_linear_singleton]
      simpa only [Nat.cast_one,m,floorCopies,p,w] using
        floor_linear_eligible P0 hC0 hn0 hRound hSqrt w aStar (fun i => (hPhi i).1) haStar hMass i)
    rw [packingTupleWeight_star,statistic_linear] at hh
    simp only [pow_one] at hh
    rw [←normalizedLinearMass_actual P0 m p] at hh
    have hTest : |(∑ i ∈ Q, aStar i)-normalizedLinearMass m p aStar| ≤
        p^(-egj13Epsilon)*normalizedLinearMass m p aStar := by
      convert hh using 1 <;> norm_num [egj13Epsilon,aStar]
    have hh' := linear_floor_test_error hC0 hn0 hτ.le hρ0 hErrorNum hRatio w aStar
      (fun i => (hPhi i).1) (fun i => (haStar i).1) Q hTest
    have hFinal := hh'.trans (mul_le_mul_of_nonneg_right hSmall
      (sum_nonneg (fun i _ => mul_nonneg (hPhi0 i) (haStar i).1)))
    rw [hSum,←hs]
    exact hFinal
  have hPaschRaw := hStats 4 (by decide) (by decide) (Sum.inr (Sum.inr ())) (by
    intro j hj hj4 R hRc
    rw [packingTupleWeight_pasch]
    have hh := floor_paschtuple_eligible_of_coefficient_window h3 hα hC hNE
      (fun T hT => (hMu T hT).1) (fun T hT => (hMu T hT).2) R (by omega) (by omega)
    simpa only [hRc] using hh)
  rw [packingTupleWeight_pasch,indexed_statistic_eq_count,tupleMass_indexed_div] at hPaschRaw
  let ψ := floorWeights A μ n
  have hPasch : |(count P:ℝ)-target ψ A| ≤ p^(-egj13Epsilon)*target ψ A := by
    convert hPaschRaw using 1 <;> norm_num [egj13Epsilon,ψ,floorWeights,P,Q,m,p]
  have htψ0 := target_nonneg_on A ψ (fun T _ => floorWeights_nonneg A μ n T)
  have hMono : target ψ A ≤ target μ A := by
    have hh := target_multiplicative_lower A ψ μ 1 (by norm_num)
      (fun T _ => floorWeights_nonneg A μ n T)
      (fun T hT => by simpa only [one_mul] using (floorWeights_bounds A μ hC0 hn0 (fun T hT => (hMu T hT).1) hT).2)
    simpa only [one_pow,one_mul] using hh
  have hUpper := raw_target_upper hC0 hnNat hMu0 (fun T hT => (hMu T hT).2) (fun e he => (hMuLoad e he).2.2)
  have hAbs := (le_abs_self _).trans (hPasch.trans (mul_le_mul_of_nonneg_right hρ1 htψ0))
  have hCount : (count P:ℝ) ≤ C^3*n^2 := by
    calc
      _ ≤ 2*target ψ A := by linarith only [hAbs]
      _ ≤ 2*target μ A := mul_le_mul_of_nonneg_left hMono (by norm_num)
      _ ≤ 2*(C^3*n^2/4) := mul_le_mul_of_nonneg_left hUpper (by norm_num)
      _ ≤ C^3*n^2 := by
        have hp : 0 ≤ C^3*n^2 := by positivity
        linarith only [hp]
  refine ⟨P,hPsub,hPpack,?_,hCount,?_⟩
  · exact sparse_leftover_of_raw_star_tests H F μ (by positivity : 0 ≤ 2*ε) hη.le
      (fun e he => ⟨(hMuLoad e he).1,(hMuLoad e he).2.2⟩) P hPpack hStars
  · intro ℓ hℓ hℓ4 k hEligible
    have hh := hStatsAll ℓ hℓ hℓ4 (Sum.inr k) (by
      simpa only [extendedPackingTupleWeight,Sum.elim_inr] using hEligible)
    dsimp only [extendedPackingTupleWeight,Sum.elim_inr] at hh
    rw [statistic_indexedTupleWeight] at hh
    convert hh using 1 <;> norm_num [egj13Epsilon,P,Q,p,n,m,A,P0,μ]

#print axioms raw_fractional_packing_with_pasch_and_tuple_tests
end TypedTriangle.Pasch
