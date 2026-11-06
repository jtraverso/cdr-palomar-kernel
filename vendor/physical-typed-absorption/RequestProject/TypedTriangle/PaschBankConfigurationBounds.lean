module
public import RequestProject.TypedTriangle.PaschBankCompletions
public import RequestProject.TypedTriangle.PaschPairExtensionBounds
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V] [DecidableEq V]

def bankTwoConfigurations (D B : Finset (Finset V)) : Finset (Finset (Finset V)) :=
  (configurations D).filter (fun K => 2 ≤ (K ∩ B).card)

def bankTouchConfigurations (D B : Finset (Finset V)) (Q : Finset V) :
    Finset (Finset (Finset V)) :=
  (configurations D).filter (fun K => Q ∈ K ∧ (K ∩ B).Nonempty)

def bankNonemptyConfigurations (D B : Finset (Finset V)) : Finset (Finset (Finset V)) :=
  (configurations D).filter (fun K => (K ∩ B).Nonempty)

theorem configurations_containing_pair_card_le (D : Finset (Finset V))
    (P : Finset (Finset V)) (hP : P.card = 2) :
    ((configurations D).filter (fun K => P ⊆ K)).card ≤ 2*Fintype.card V := by
  obtain ⟨Q,T,hQT,rfl⟩ := card_eq_two.mp hP
  simpa only [pairExtensions,insert_subset_iff,singleton_subset_iff] using
    pairExtensions_card_le D Q T hQT

theorem bankTwoConfigurations_card_le (D B : Finset (Finset V)) :
    (bankTwoConfigurations D B).card ≤ 2*Fintype.card V*(overlappingBankPairs B).card := by
  let C := (overlappingBankPairs B).biUnion
    (fun P => (configurations D).filter (fun K => P ⊆ K))
  have hSub : bankTwoConfigurations D B ⊆ C := by
    intro K hK
    obtain ⟨hConf,hCard⟩ := mem_filter.mp hK
    have hPasch := (mem_configurations.mp hConf).2.2
    obtain ⟨P,hPsub,hPc⟩ := exists_subset_card_eq hCard
    have hPK : P ⊆ K := hPsub.trans inter_subset_left
    have hPB : P ⊆ B := hPsub.trans inter_subset_right
    have hP : P ∈ overlappingBankPairs B := by
      obtain ⟨Q,T,hQT,hPair⟩ := card_eq_two.mp hPc
      have hQP : Q ∈ P := by rw [hPair]; simp
      have hTP : T ∈ P := by rw [hPair]; simp
      apply mem_filter.mpr
      exact ⟨mem_powersetCard.mpr ⟨hPB,hPc⟩,Q,hQP,T,hTP,hQT,
        inter_nonempty hPasch (hPK hQP) (hPK hTP) hQT⟩
    exact mem_biUnion.mpr ⟨P,hP,mem_filter.mpr ⟨hConf,hPK⟩⟩
  calc
    _ ≤ C.card := card_le_card hSub
    _ ≤ ∑ P ∈ overlappingBankPairs B,
        ((configurations D).filter (fun K => P ⊆ K)).card := card_biUnion_le
    _ ≤ ∑ _P ∈ overlappingBankPairs B, 2*Fintype.card V := by
      apply sum_le_sum
      intro P hP
      exact configurations_containing_pair_card_le D P
        (mem_powersetCard.mp (mem_filter.mp hP).1).2
    _ = _ := by simp [Nat.mul_comm]

theorem bankTouchConfigurations_card_le (D B : Finset (Finset V)) (Q : Finset V)
    (hQ : Q ∉ B) :
    (bankTouchConfigurations D B Q).card ≤ 2*Fintype.card V*(touchingBank B Q).card := by
  let C := (touchingBank B Q).biUnion (fun T => pairExtensions D Q T)
  have hSub : bankTouchConfigurations D B Q ⊆ C := by
    intro K hK
    obtain ⟨hConf,hQK,T,hTKB⟩ := mem_filter.mp hK
    obtain ⟨hTK,hTB⟩ := mem_inter.mp hTKB
    have hQT : Q ≠ T := by rintro rfl; exact hQ hTB
    have hTouch : T ∈ touchingBank B Q := mem_filter.mpr
      ⟨hTB,inter_nonempty (mem_configurations.mp hConf).2.2 hTK hQK hQT.symm⟩
    exact mem_biUnion.mpr ⟨T,hTouch,mem_filter.mpr ⟨hConf,hQK,hTK⟩⟩
  calc
    _ ≤ C.card := card_le_card hSub
    _ ≤ ∑ T ∈ touchingBank B Q, (pairExtensions D Q T).card := card_biUnion_le
    _ ≤ ∑ _T ∈ touchingBank B Q, 2*Fintype.card V := by
      apply sum_le_sum
      intro T hT
      have hQT : Q ≠ T := by
        rintro rfl
        exact hQ (mem_filter.mp hT).1
      exact pairExtensions_card_le D Q T hQT
    _ = _ := by simp [Nat.mul_comm]

theorem bankNonemptyConfigurations_card_le (D B : Finset (Finset V))
    (hB : ∀ Q ∈ B, Q.card = 3) :
    (bankNonemptyConfigurations D B).card ≤ (Fintype.card V)^3*B.card := by
  let C := B.biUnion (fun Q => (configurations D).filter (fun K => Q ∈ K))
  have hSub : bankNonemptyConfigurations D B ⊆ C := by
    intro K hK
    obtain ⟨hConf,Q,hQ⟩ := mem_filter.mp hK
    obtain ⟨hQK,hQB⟩ := mem_inter.mp hQ
    exact mem_biUnion.mpr ⟨Q,hQB,mem_filter.mpr ⟨hConf,hQK⟩⟩
  calc
    _ ≤ C.card := card_le_card hSub
    _ ≤ ∑ Q ∈ B, ((configurations D).filter (fun K => Q ∈ K)).card := card_biUnion_le
    _ ≤ ∑ _Q ∈ B, (Fintype.card V)^3 := by
      apply sum_le_sum
      intro Q hQ
      exact rootedCount_le_cube D Q (hB Q hQ)
    _ = _ := by simp [Nat.mul_comm]

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.configurations_containing_pair_card_le
#print axioms TypedTriangle.Pasch.bankTwoConfigurations_card_le
#print axioms TypedTriangle.Pasch.bankTouchConfigurations_card_le
#print axioms TypedTriangle.Pasch.bankNonemptyConfigurations_card_le
