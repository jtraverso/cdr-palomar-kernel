module
public import RequestProject.TypedTriangle.PaschBankIncidence
public import RequestProject.TypedTriangle.PaschTwoNewCompletions
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

/-- Old blocks containing two distinct crossing points from Q and T. -/
def crossCandidates (B : Finset (Finset V)) (Q T : Finset V) : Finset (Finset V) :=
  Q.biUnion (fun a => T.biUnion (fun b =>
    if a = b then ∅ else B.filter (fun U => a ∈ U ∧ b ∈ U)))

theorem crossCandidates_subset (B : Finset (Finset V)) (Q T : Finset V) :
    crossCandidates B Q T ⊆ B := by
  intro U hU
  obtain ⟨a,ha,hU⟩ := mem_biUnion.mp hU
  obtain ⟨b,hb,hU⟩ := mem_biUnion.mp hU
  split_ifs at hU with hab
  · simp at hU
  · exact (mem_filter.mp hU).1

theorem crossCandidates_card_le (B : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound B L) (Q T : Finset V) :
    (crossCandidates B Q T).card ≤ Q.card*T.card*L := by
  calc
    _ ≤ ∑ a ∈ Q, (T.biUnion (fun b =>
        if a = b then ∅ else B.filter (fun U => a ∈ U ∧ b ∈ U))).card := card_biUnion_le
    _ ≤ ∑ _a ∈ Q, T.card*L := by
      apply sum_le_sum
      intro a ha
      apply card_biUnion_le.trans
      calc
        _ ≤ ∑ _b ∈ T, L := by
          apply sum_le_sum
          intro b hb
          split_ifs with hab
          · simp
          · exact hL a b hab
        _ = T.card*L := by simp
    _ = _ := by simp [Nat.mul_assoc]

/-- The two intersections with a third block are different: otherwise the
common vertex would lie in three blocks instead of two. -/
theorem IsPasch.crossing_intersections_ne {K : Finset (Finset V)} (hK : IsPasch K)
    {Q T U : Finset V} (hQ : Q ∈ K) (hT : T ∈ K) (hU : U ∈ K)
    (hQT : Q ≠ T) (hUQ : U ≠ Q) (hUT : U ≠ T)
    {a b : V} (haQ : a ∈ Q) (haU : a ∈ U) (hbT : b ∈ T) (hbU : b ∈ U) : a ≠ b := by
  intro hab
  subst b
  have hSub : ({Q,T,U} : Finset (Finset V)) ⊆ K.filter (fun C => a ∈ C) := by
    intro C hC
    simp only [mem_insert,mem_singleton] at hC
    rcases hC with rfl | rfl | rfl
    · exact mem_filter.mpr ⟨hQ,haQ⟩
    · exact mem_filter.mpr ⟨hT,hbT⟩
    · exact mem_filter.mpr ⟨hU,haU⟩
  have hCard : ({Q,T,U} : Finset (Finset V)).card = 3 := by
    simp [hQT,hUQ,hUT,Ne.symm hUQ,Ne.symm hUT]
  have hDegree := hK.degree_zero_or_two a
  have hh := card_le_card hSub
  omega

theorem IsPasch.third_mem_crossCandidates {K : Finset (Finset V)} (hK : IsPasch K)
    {B : Finset (Finset V)} {Q T U : Finset V}
    (hQ : Q ∈ K) (hT : T ∈ K) (hU : U ∈ K)
    (hQT : Q ≠ T) (hUQ : U ≠ Q) (hUT : U ≠ T) (hUB : U ∈ B) :
    U ∈ crossCandidates B Q T := by
  obtain ⟨a,ha⟩ := inter_nonempty hK hU hQ hUQ
  obtain ⟨b,hb⟩ := inter_nonempty hK hU hT hUT
  obtain ⟨haU,haQ⟩ := mem_inter.mp ha
  obtain ⟨hbU,hbT⟩ := mem_inter.mp hb
  have hab := hK.crossing_intersections_ne hQ hT hU hQT hUQ hUT haQ haU hbT hbU
  apply mem_biUnion.mpr
  refine ⟨a,haQ,mem_biUnion.mpr ⟨b,hbT,?_⟩⟩
  rw [if_neg hab]
  exact mem_filter.mpr ⟨hUB,haU,hbU⟩

def compatibleOldPairsAround (B : Finset (Finset V)) (Q : Finset V) :
    Finset (Finset (Finset V)) :=
  (B.powersetCard 2).filter (fun S => ∃ K, IsPasch K ∧ Q ∈ K ∧ S ⊆ K)

def compatibleOldTriples (B : Finset (Finset V)) : Finset (Finset (Finset V)) :=
  (B.powersetCard 3).filter (fun S => ∃ K, IsPasch K ∧ S ⊆ K)

theorem mem_compatibleOldPairsAround (B : Finset (Finset V)) (Q : Finset V)
    (S : Finset (Finset V)) :
    S ∈ compatibleOldPairsAround B Q ↔
      S ⊆ B ∧ S.card = 2 ∧ ∃ K, IsPasch K ∧ Q ∈ K ∧ S ⊆ K := by
  simp only [compatibleOldPairsAround,mem_filter,mem_powersetCard,and_assoc]

theorem mem_compatibleOldTriples (B : Finset (Finset V)) (S : Finset (Finset V)) :
    S ∈ compatibleOldTriples B ↔
      S ⊆ B ∧ S.card = 3 ∧ ∃ K, IsPasch K ∧ S ⊆ K := by
  simp only [compatibleOldTriples,mem_filter,mem_powersetCard,and_assoc]

/-- The selected old pair, together with the external root block, fixes
the actual configuration; this is not a count of arbitrary ordered witnesses. -/
theorem IsPasch.eq_of_root_and_old_pair {K K' : Finset (Finset V)}
    (hK : IsPasch K) (hK' : IsPasch K')
    {B : Finset (Finset V)} {Q : Finset V} {P : Finset (Finset V)}
    (hQ : Q ∉ B) (hPc : P.card = 2) (hPB : P ⊆ B)
    (hQK : Q ∈ K) (hQK' : Q ∈ K') (hPK : P ⊆ K) (hPK' : P ⊆ K') : K = K' := by
  have hQP : Q ∉ P := fun h => hQ (hPB h)
  apply hK.eq_of_common_triple hK' (K := insert Q P)
  · rw [card_insert_of_notMem hQP,hPc]
  · exact insert_subset_iff.mpr ⟨hQK,hPK⟩
  · exact insert_subset_iff.mpr ⟨hQK',hPK'⟩

def bankPairConfigurations (D B : Finset (Finset V)) (Q : Finset V) :
    Finset (Finset (Finset V)) :=
  (configurations D).filter (fun K => Q ∈ K ∧ 2 ≤ (K ∩ B).card)

def bankTripleConfigurations (D B : Finset (Finset V)) : Finset (Finset (Finset V)) :=
  (configurations D).filter (fun K => 3 ≤ (K ∩ B).card)

section Finite
variable [Fintype V]

theorem compatibleOldPairsAround_card_le (B : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound B L) (hB : ∀ T ∈ B, T.card = 3)
    (Q : Finset V) (hQ : Q ∉ B) (hQc : Q.card = 3) :
    (compatibleOldPairsAround B Q).card ≤ 27*Fintype.card V*L^2 := by
  let C := (touchingBank B Q).biUnion (fun T =>
    (crossCandidates B Q T).image (fun U => ({T,U} : Finset (Finset V))))
  have hSub : compatibleOldPairsAround B Q ⊆ C := by
    intro S hS
    obtain ⟨hSB,hSc,K,hK,hQK,hSK⟩ := (mem_compatibleOldPairsAround B Q S).mp hS
    obtain ⟨T,U,hTU,rfl⟩ := card_eq_two.mp hSc
    have hTB : T ∈ B := hSB (by simp)
    have hUB : U ∈ B := hSB (by simp)
    have hTK : T ∈ K := hSK (by simp)
    have hUK : U ∈ K := hSK (by simp)
    have hTQ : T ≠ Q := by rintro rfl; exact hQ hTB
    have hUQ : U ≠ Q := by rintro rfl; exact hQ hUB
    have hTouch : T ∈ touchingBank B Q :=
      mem_filter.mpr ⟨hTB,inter_nonempty hK hTK hQK hTQ⟩
    have hCross := hK.third_mem_crossCandidates hQK hTK hUK hTQ.symm hUQ hTU.symm hUB
    exact mem_biUnion.mpr ⟨T,hTouch,mem_image.mpr ⟨U,hCross,rfl⟩⟩
  have hTouch : (touchingBank B Q).card ≤ 3*Fintype.card V*L := by
    simpa only [hQc] using touchingBank_card_le B L hL hB Q
  calc
    _ ≤ C.card := card_le_card hSub
    _ ≤ ∑ T ∈ touchingBank B Q,
        ((crossCandidates B Q T).image (fun U => ({T,U} : Finset (Finset V)))).card := card_biUnion_le
    _ ≤ ∑ T ∈ touchingBank B Q, (crossCandidates B Q T).card :=
      sum_le_sum (fun _ _ => card_image_le)
    _ ≤ ∑ _T ∈ touchingBank B Q, 9*L := by
      apply sum_le_sum
      intro T hT
      have hTc := hB T (mem_filter.mp hT).1
      simpa only [hQc,hTc,show 3*3=9 by decide] using crossCandidates_card_le B L hL Q T
    _ = (touchingBank B Q).card*(9*L) := by simp
    _ ≤ (3*Fintype.card V*L)*(9*L) := Nat.mul_le_mul_right _ hTouch
    _ = _ := by ring

theorem compatibleOldTriples_card_le (B : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound B L) (hB : ∀ T ∈ B, T.card = 3) :
    (compatibleOldTriples B).card ≤ 27*Fintype.card V*L^2*B.card := by
  let C := B.biUnion (fun Q => (touchingBank B Q).biUnion (fun T =>
    (crossCandidates B Q T).image (fun U => ({Q,T,U} : Finset (Finset V)))))
  have hSub : compatibleOldTriples B ⊆ C := by
    intro S hS
    obtain ⟨hSB,hSc,K,hK,hSK⟩ := (mem_compatibleOldTriples B S).mp hS
    obtain ⟨Q,T,U,hQT,hQU,hTU,rfl⟩ := card_eq_three.mp hSc
    have hQB : Q ∈ B := hSB (by simp)
    have hTB : T ∈ B := hSB (by simp)
    have hUB : U ∈ B := hSB (by simp)
    have hQK : Q ∈ K := hSK (by simp)
    have hTK : T ∈ K := hSK (by simp)
    have hUK : U ∈ K := hSK (by simp)
    have hTouch : T ∈ touchingBank B Q :=
      mem_filter.mpr ⟨hTB,inter_nonempty hK hTK hQK hQT.symm⟩
    have hCross := hK.third_mem_crossCandidates hQK hTK hUK hQT hQU.symm hTU.symm hUB
    exact mem_biUnion.mpr ⟨Q,hQB,mem_biUnion.mpr ⟨T,hTouch,mem_image.mpr ⟨U,hCross,rfl⟩⟩⟩
  calc
    _ ≤ C.card := card_le_card hSub
    _ ≤ ∑ Q ∈ B, ((touchingBank B Q).biUnion (fun T =>
        (crossCandidates B Q T).image (fun U => ({Q,T,U} : Finset (Finset V))))).card := card_biUnion_le
    _ ≤ ∑ _Q ∈ B, 27*Fintype.card V*L^2 := by
      apply sum_le_sum
      intro Q hQ
      have hQc := hB Q hQ
      have hTouch : (touchingBank B Q).card ≤ 3*Fintype.card V*L := by
        simpa only [hQc] using touchingBank_card_le B L hL hB Q
      calc
        _ ≤ ∑ T ∈ touchingBank B Q,
            ((crossCandidates B Q T).image (fun U => ({Q,T,U} : Finset (Finset V)))).card := card_biUnion_le
        _ ≤ ∑ T ∈ touchingBank B Q, (crossCandidates B Q T).card :=
          sum_le_sum (fun _ _ => card_image_le)
        _ ≤ ∑ _T ∈ touchingBank B Q, 9*L := by
          apply sum_le_sum
          intro T hT
          have hTc := hB T (mem_filter.mp hT).1
          simpa only [hQc,hTc,show 3*3=9 by decide] using crossCandidates_card_le B L hL Q T
        _ = (touchingBank B Q).card*(9*L) := by simp
        _ ≤ (3*Fintype.card V*L)*(9*L) := Nat.mul_le_mul_right _ hTouch
        _ = _ := by ring
    _ = _ := by simp [Nat.mul_comm]

theorem bankPairConfigurations_card_le (D B : Finset (Finset V)) (Q : Finset V)
    (hQ : Q ∉ B) :
    (bankPairConfigurations D B Q).card ≤ (compatibleOldPairsAround B Q).card := by
  let C := bankPairConfigurations D B Q
  have hWitness : ∀ K ∈ C, ∃ P ∈ compatibleOldPairsAround B Q, P ⊆ K := by
    intro K hK
    obtain ⟨hConf,hQK,hCard⟩ := mem_filter.mp hK
    obtain ⟨P,hPsub,hPc⟩ := exists_subset_card_eq hCard
    have hPK : P ⊆ K := hPsub.trans inter_subset_left
    have hPB : P ⊆ B := hPsub.trans inter_subset_right
    exact ⟨P,(mem_compatibleOldPairsAround B Q P).mpr ⟨hPB,hPc,
      K,(mem_configurations.mp hConf).2.2,hQK,hPK⟩,hPK⟩
  let f : ↥C → ↥(compatibleOldPairsAround B Q) := fun K =>
    ⟨Classical.choose (hWitness K.val K.property),
      (Classical.choose_spec (hWitness K.val K.property)).1⟩
  have hf : Function.Injective f := by
    intro K K' heq
    have hPP : (f K).val = (f K').val := congrArg Subtype.val heq
    have hPK : (f K).val ⊆ K.val := (Classical.choose_spec (hWitness K.val K.property)).2
    have hPK' : (f K).val ⊆ K'.val := by
      rw [hPP]
      exact (Classical.choose_spec (hWitness K'.val K'.property)).2
    obtain ⟨hPB,hPc,_⟩ := (mem_compatibleOldPairsAround B Q (f K).val).mp (f K).property
    obtain ⟨hConf,hQK,_⟩ := mem_filter.mp K.property
    obtain ⟨hConf',hQK',_⟩ := mem_filter.mp K'.property
    apply Subtype.ext
    exact ((mem_configurations.mp hConf).2.2).eq_of_root_and_old_pair
      ((mem_configurations.mp hConf').2.2) hQ hPc hPB hQK hQK' hPK hPK'
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem bankTripleConfigurations_card_le (D B : Finset (Finset V)) :
    (bankTripleConfigurations D B).card ≤ (compatibleOldTriples B).card := by
  let C := bankTripleConfigurations D B
  have hWitness : ∀ K ∈ C, ∃ P ∈ compatibleOldTriples B, P ⊆ K := by
    intro K hK
    obtain ⟨hConf,hCard⟩ := mem_filter.mp hK
    obtain ⟨P,hPsub,hPc⟩ := exists_subset_card_eq hCard
    have hPK : P ⊆ K := hPsub.trans inter_subset_left
    have hPB : P ⊆ B := hPsub.trans inter_subset_right
    exact ⟨P,(mem_compatibleOldTriples B P).mpr ⟨hPB,hPc,
      K,(mem_configurations.mp hConf).2.2,hPK⟩,hPK⟩
  let f : ↥C → ↥(compatibleOldTriples B) := fun K =>
    ⟨Classical.choose (hWitness K.val K.property),
      (Classical.choose_spec (hWitness K.val K.property)).1⟩
  have hf : Function.Injective f := by
    intro K K' heq
    have hPP : (f K).val = (f K').val := congrArg Subtype.val heq
    have hPK : (f K).val ⊆ K.val := (Classical.choose_spec (hWitness K.val K.property)).2
    have hPK' : (f K).val ⊆ K'.val := by
      rw [hPP]
      exact (Classical.choose_spec (hWitness K'.val K'.property)).2
    obtain ⟨_,hPc,_⟩ := (mem_compatibleOldTriples B (f K).val).mp (f K).property
    obtain ⟨hConf,_⟩ := mem_filter.mp K.property
    obtain ⟨hConf',_⟩ := mem_filter.mp K'.property
    apply Subtype.ext
    exact ((mem_configurations.mp hConf).2.2).eq_of_common_triple
      ((mem_configurations.mp hConf').2.2) hPc hPK hPK'
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

end Finite
end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.crossCandidates_card_le
#print axioms TypedTriangle.Pasch.IsPasch.third_mem_crossCandidates
#print axioms TypedTriangle.Pasch.compatibleOldPairsAround_card_le
#print axioms TypedTriangle.Pasch.compatibleOldTriples_card_le
#print axioms TypedTriangle.Pasch.IsPasch.eq_of_root_and_old_pair
#print axioms TypedTriangle.Pasch.bankPairConfigurations_card_le
#print axioms TypedTriangle.Pasch.bankTripleConfigurations_card_le
