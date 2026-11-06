module
public import RequestProject.TypedTriangle.PaschPackingModel
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedClone WeightedStar
variable {V I : Type*} [Fintype V]

def rawProfileConstant (a b : ℝ) : ℝ := max 1 (max (2/a) b)

def rawPaschPackingCost (a b : ℝ) : ℝ := (rawProfileConstant a b)^3

theorem rawProfileConstant_one_le (a b : ℝ) : 1 ≤ rawProfileConstant a b := le_max_left _ _

theorem raw_normalized_coefficient_window {a b ε n x : ℝ} (ha : 0 < a)
    (hε : 0 ≤ ε) (hεHalf : ε ≤ 1/2) (hn : 0 < n) (hx : a/n ≤ x ∧ x ≤ b/n) :
    1/(rawProfileConstant a b*n) ≤ x/(1+ε) ∧ x/(1+ε) ≤ rawProfileConstant a b/n := by
  let C := rawProfileConstant a b
  have hC1 : 1 ≤ C := rawProfileConstant_one_le a b
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hCa : 2/a ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCb : b ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hDen : 0 < 1+ε := by linarith only [hε]
  have hx0 : 0 ≤ x := (by positivity : (0:ℝ) ≤ a/n).trans hx.1
  constructor
  · have hAC : 2 ≤ C*a := (div_le_iff₀ ha).mp hCa
    have hBase : 1/(C*n) ≤ (a/n)/2 := by
      apply (div_le_iff₀ (by positivity : 0 < C*n)).mpr
      have hh := mul_le_mul_of_nonneg_right hAC (by norm_num : (0:ℝ) ≤ 1/2)
      have he : ((a/n)/2)*(C*n) = C*a/2 := by field_simp [ne_of_gt hn] <;> ring
      rw [he]
      linarith only [hh]
    exact hBase.trans ((div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ a/n) hDen
      (by linarith only [hεHalf] : 1+ε ≤ 2)).trans (div_le_div_of_nonneg_right hx.1 hDen.le))
  · exact (div_le_self hx0 (by linarith only [hε])).trans
      (hx.2.trans (div_le_div_of_nonneg_right hCb hn.le))

theorem raw_normalized_load_window {ε t : ℝ} (hε : 0 ≤ ε) (hεHalf : ε ≤ 1/2)
    (ht : |t-1| ≤ ε) : 1-2*ε ≤ t/(1+ε) ∧ 1/3 ≤ t/(1+ε) ∧ t/(1+ε) ≤ 1 := by
  have hDen : 0 < 1+ε := by linarith only [hε]
  have hb := abs_le.mp ht
  constructor
  · apply (le_div_iff₀ hDen).mpr
    nlinarith only [hb.1,sq_nonneg ε]
  constructor
  · apply (le_div_iff₀ hDen).mpr
    linarith only [hb.1,hεHalf]
  · exact (div_le_one hDen).mpr (by linarith only [hb.2])

theorem bdry_div_constant (H : Host V I) (F : Set (Multiset I)) (μ : Finset V → ℝ)
    (d : ℝ) (e : Sym2 V) : bdry H F (fun T => μ T/d) e = bdry H F μ e/d := by
  simp only [bdry_eq_sum_triOn,sum_div]

theorem indexed_load_eq_bdry (H : Host V I) (F : Set (Multiset I)) (μ : Finset V → ℝ)
    (e : Sym2 V) : (∑ i : allowed H F, if e ∈ indexedPackets (allowed H F) i then μ i.val else 0) =
      bdry H F μ e := by
  simpa only [bdry_eq_sum_triOn,triOn] using indexed_load_eq (allowed H F) μ e

theorem target_lower_of_coefficient_window {H : Host V I} {F : Set (Multiset I)}
    {α C : ℝ} {μ : Finset V → ℝ} (hLow : ∀ T, IsAllowed H F T → 1/(C*Fintype.card V) ≤ μ T)
    (hH3 : CommonNbrCond H F α) (hα : 0 < α) (hC : 0 < C)
    (hN : supersaturationOrder α ≤ Fintype.card V)
    {a b c : V} (hT : IsAllowed H F {a,b,c}) :
    massConstant α C * (Fintype.card V : ℝ)^2 ≤ target μ (allowed H F) := by
  let n := (Fintype.card V : ℝ)
  have hnNat : 0 < Fintype.card V := by
    have hs : 6 ≤ Fintype.card V := (le_max_left _ _).trans hN
    omega
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast hnNat
  have hc := count_lower_of_common_neighbors hH3 hα hN hT
  have hbase : 0 ≤ 1/(C*n) := by positivity
  have hterm : ∀ S ∈ configurations (allowed H F), (1/(C*n))^4 ≤ ∏ T ∈ S, μ T := by
    intro S hS
    obtain ⟨hSub,hCard,hPasch⟩ := mem_configurations.mp hS
    calc
      (1/(C*n))^4 = ∏ _T ∈ S, 1/(C*n) := by simp [hCard]
      _ ≤ _ := prod_le_prod₀ (fun _ _ => hbase)
        (fun T hT => (hLow T ((mem_filter.mp (hSub hT)).2)))
  have hm : (1/(C*n))^4 * count (allowed H F) ≤ target μ (allowed H F) := by
    rw [target,statistic_eq_sum]
    calc
      _ = ∑ _S ∈ configurations (allowed H F), (1/(C*n))^4 := by simp [count,mul_comm]
      _ ≤ _ := sum_le_sum hterm
  have hcp := mul_le_mul_of_nonneg_left hc (pow_nonneg hbase 4)
  have heq : (1/(C*n))^4 * (α^24*n^6/(2*6^6)) = massConstant α C * n^2 := by
    unfold massConstant
    field_simp [ne_of_gt hC,ne_of_gt hn]
    <;> ring
  change (1/(C*n))^4 * (α^24*n^6/(2*6^6)) ≤ _ at hcp
  rw [heq] at hcp
  exact hcp.trans hm

theorem floor_paschtuple_eligible_of_coefficient_window {I : Type*} {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {α C : ℝ} (hH3 : CommonNbrCond H F α) (hα : 0 < α) (hC : 1 ≤ C)
    (hN : floorEligibilityOrder α C ≤ Fintype.card V)
    (hLow : ∀ T ∈ allowed H F, 1/(C*Fintype.card V) ≤ μ T)
    (hUp : ∀ T ∈ allowed H F, μ T ≤ C/Fintype.card V)
    (R : Finset (allowed H F)) (hR1 : 1 ≤ R.card) (hR4 : R.card ≤ 4) :
    let n := (Fintype.card V:ℝ)
    tupleExtensionMass (indexedPackets (allowed H F)) (floorCopies (allowed H F) μ n)
      (indexedWeight (allowed H F)) 4 R * (n^2)^((R.card:ℝ)+(1/4:ℝ)) ≤
        tupleMass (indexedPackets (allowed H F)) (floorCopies (allowed H F) μ n)
          (indexedWeight (allowed H F)) 4 := by
  let D := allowed H F
  let n := (Fintype.card V:ℝ)
  have hNsup : supersaturationOrder α ≤ Fintype.card V := by
    unfold floorEligibilityOrder at hN
    omega
  have hnNat : 1 ≤ Fintype.card V := by
    unfold floorEligibilityOrder at hN
    omega
  have hn : 1 ≤ n := by dsimp only [n]; exact_mod_cast hnNat
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hc : 0 < massConstant α C := by unfold massConstant; positivity
  have hRound : 2*C ≤ n := by
    apply Nat.ceil_le.mp
    unfold floorEligibilityOrder at hN
    omega
  have hScale : 32*C^3 ≤ massConstant α C*n := by
    have hh : 32*C^3/massConstant α C ≤ n := by
      apply Nat.ceil_le.mp
      unfold floorEligibilityOrder at hN
      omega
    exact ((div_le_iff₀ hc).mp hh).trans_eq (mul_comm _ _)
  obtain ⟨i,hi⟩ := card_pos.mp (show 0 < R.card by omega)
  have hAllowed := isAllowed_of_mem_allowed i.property
  obtain ⟨a,b,c,hab,hac,hbc,hEq⟩ := card_eq_three.mp hAllowed.1
  have hRoot : IsAllowed H F {a,b,c} := hEq ▸ hAllowed
  have hSource := target_lower_of_coefficient_window
    (fun T hT => hLow T (mem_filter.mpr ⟨mem_univ _,hT⟩)) hH3 hα hC0 hNsup hRoot
  have hRounded := floorWeights_target_lower D μ hC0 hn0 (by linarith only [hRound,hC0]) hLow
  have hGamma := gamma_sqrt_le_rounded_mass hC0.le hc.le hn hRound hScale (le_refl (2*C^3))
    hSource hRounded
  have hDegree := floor_actual_extension_le D μ hC hnNat rfl
    (fun T hT => (isAllowed_of_mem_allowed hT).1) hLow hUp R hR1 hR4
  have hMass := le_of_eq (floor_actual_mass D μ hn0)
  exact tuple_eligibility_of_gamma_sqrt hn0 hR4 hDegree hMass hGamma


theorem raw_star_sum (H : Host V I) (F : Set (Multiset I)) (μ : Finset V → ℝ) (v : V) :
    2*(∑ T ∈ allowed H F, μ T*starWeight v T) =
      ∑ w ∈ nbrsIn (edges H) v, bdry H F μ s(v,w) := by
  have hs : (∑ w ∈ univ.erase v, bdry H F μ s(v,w)) =
      ∑ w ∈ nbrsIn (edges H) v, bdry H F μ s(v,w) := by
    rw [nbrsIn,sum_filter]
    apply sum_congr rfl
    intro w hw
    by_cases he : s(v,w) ∈ edges H
    · simp only [if_pos he]
    · simp only [if_neg he,bdry_eq_zero_of_not_mem H F μ he]
  rw [←hs,sum_nbrs_bdry]
  simp only [triAt,sum_filter,starWeight,mul_ite,mul_one,mul_zero]

theorem raw_star_bounds {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ}
    {l : ℝ} (hLoad : ∀ e ∈ edges H, l ≤ bdry H F μ e ∧ bdry H F μ e ≤ 1) (v : V) :
    l*(nbrsIn (edges H) v).card ≤ 2*(∑ T ∈ allowed H F, μ T*starWeight v T) ∧
      2*(∑ T ∈ allowed H F, μ T*starWeight v T) ≤ (nbrsIn (edges H) v).card := by
  rw [raw_star_sum]
  constructor
  · have hh := sum_le_sum (s:=nbrsIn (edges H) v) (fun w hw => (hLoad s(v,w) (mem_filter.mp hw).2).1)
    simpa only [sum_const,nsmul_eq_mul,mul_comm] using hh
  · have hh := sum_le_sum (s:=nbrsIn (edges H) v) (fun w hw => (hLoad s(v,w) (mem_filter.mp hw).2).2)
    simpa only [sum_const,nsmul_eq_mul,mul_one] using hh

theorem raw_star_zero_or_lower {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ}
    {α : ℝ} (h3 : CommonNbrCond H F α)
    (hLoad : ∀ e ∈ edges H, 1/3 ≤ bdry H F μ e ∧ bdry H F μ e ≤ 1) (v : V) :
    (∑ T ∈ allowed H F, μ T*starWeight v T) = 0 ∨
      α/6*Fintype.card V ≤ ∑ T ∈ allowed H F, μ T*starWeight v T := by
  by_cases hv : ActiveRoot H F v
  · have hd := active_degree_lower h3 hv
    have hs := (raw_star_bounds hLoad v).1
    right
    nlinarith only [hd,hs]
  · left
    apply sum_eq_zero
    intro T hT
    have hvT : v ∉ T := fun hvT => hv ⟨T,isAllowed_of_mem_allowed hT,hvT⟩
    simp only [starWeight,if_neg hvT,mul_zero]

theorem sparse_leftover_of_raw_star_tests (H : Host V I) (F : Set (Multiset I))
    (φ : Finset V → ℝ) {κ η : ℝ} (hκ : 0 ≤ κ) (hη : 0 ≤ η)
    (hLoad : ∀ e ∈ edges H, 1-κ ≤ bdry H F φ e ∧ bdry H F φ e ≤ 1)
    (P : Finset (Finset V)) (hP : IsPacking H F P)
    (hstar : ∀ v, |(∑ T ∈ P, starWeight v T)-(∑ T ∈ allowed H F, φ T*starWeight v T)| ≤
      η*(∑ T ∈ allowed H F, φ T*starWeight v T)) :
    ∀ v, (((edges H \ P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ (κ+η)*Fintype.card V := by
  intro v
  have hPE : P.biUnion triEdges ⊆ edges H := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  have hsub : nbrsIn (P.biUnion triEdges) v ⊆ nbrsIn (edges H) v := by
    intro w hw
    exact mem_filter.mpr ⟨(mem_filter.mp hw).1,hPE (mem_filter.mp hw).2⟩
  have hd : nbrsIn (edges H \ P.biUnion triEdges) v = nbrsIn (edges H) v \ nbrsIn (P.biUnion triEdges) v := by
    ext w
    simp only [nbrsIn,mem_filter,mem_sdiff]
    tauto
  have hloop : ∀ e ∈ edges H \ P.biUnion triEdges, ¬e.IsDiag := by
    intro e he
    have hh := (mem_filter.mp (mem_sdiff.mp he).1).2
    exact H.G.not_isDiag_of_mem_edgeSet hh
  rw [incident_card_eq_nbrs _ v hloop,hd,card_sdiff_of_subset hsub,Nat.cast_sub (card_le_card hsub)]
  have hc := packing_star_count hP v
  have hcR : ((nbrsIn (P.biUnion triEdges) v).card:ℝ) = 2*(∑ T ∈ P, starWeight v T) := by
    rw [←hc]
    push_cast
    simp [starWeight,sum_filter]
  have hs := raw_star_bounds hLoad v
  have hbound : ((nbrsIn (edges H) v).card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ _
  have herr := (le_abs_self _).trans (hstar v)
  have herr' := (neg_le_abs _).trans (hstar v)
  have hmul := mul_le_mul_of_nonneg_left hbound (add_nonneg hκ hη)
  have hEta := mul_le_mul_of_nonneg_left hs.2 hη
  rw [hcR]
  nlinarith only [hs.1,hEta,herr',hmul]

theorem raw_profile_mass_cap {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ}
    (hμ : ∀ T ∈ allowed H F, 0 ≤ μ T)
    (hLoad : ∀ e ∈ edges H, bdry H F μ e ≤ 1) :
    (∑ T ∈ allowed H F, μ T) ≤ (Fintype.card V:ℝ)^2 := by
  let D := allowed H F
  have hAll (e : Sym2 V) : (∑ i : D, if e ∈ indexedPackets D i then μ i.val else 0) ≤ 1 := by
    rw [indexed_load_eq_bdry]
    by_cases he : e ∈ edges H
    · exact hLoad e he
    · rw [bdry_eq_zero_of_not_mem H F μ he]
      norm_num
  have hCap := fractional_total_mass_cap (indexedPackets D) (fun i => μ i.val)
    (fun i => hμ i.val i.property)
    (fun i => card_pos.mp (by rw [indexedPackets_uniform D (fun T hT => (isAllowed_of_mem_allowed hT).1)]; decide)) hAll
  have hs : (∑ i : D, μ i.val) = ∑ T ∈ allowed H F, μ T := sum_coe_sort D μ
  rw [hs] at hCap
  exact hCap.trans (by exact_mod_cast (sym2_card_le_square (V:=V)))

theorem raw_target_upper {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ} {C : ℝ}
    (hC : 0 < C) (hn : 0 < Fintype.card V)
    (hμ0 : ∀ T ∈ allowed H F, 0 ≤ μ T)
    (hμb : ∀ T ∈ allowed H F, μ T ≤ C/Fintype.card V)
    (hLoad : ∀ e ∈ edges H, bdry H F μ e ≤ 1) :
    target μ (allowed H F) ≤ C^3*(Fintype.card V:ℝ)^2/4 := by
  have hh := target_le_cube_times_seed_mass (allowed H F) μ hC.le hn
    (fun T hT => (isAllowed_of_mem_allowed hT).1) hμ0 hμb
  have hm := mul_le_mul_of_nonneg_left (raw_profile_mass_cap hμ0 hLoad) (pow_nonneg hC.le 3)
  linarith only [hh,hm]


#print axioms rawProfileConstant_one_le
#print axioms raw_normalized_coefficient_window
#print axioms raw_normalized_load_window
#print axioms bdry_div_constant
#print axioms indexed_load_eq_bdry
#print axioms target_lower_of_coefficient_window
#print axioms floor_paschtuple_eligible_of_coefficient_window
#print axioms raw_star_sum
#print axioms raw_star_bounds
#print axioms raw_star_zero_or_lower
#print axioms sparse_leftover_of_raw_star_tests
#print axioms raw_profile_mass_cap
#print axioms raw_target_upper
end TypedTriangle.Pasch
