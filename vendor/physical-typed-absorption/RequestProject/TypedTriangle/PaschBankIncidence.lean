module
public import RequestProject.TypedTriangle.PaschEdgeAveraging
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V] [DecidableEq V]

def touchingBank (B : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  B.filter (fun Q => (Q ∩ T).Nonempty)

def overlappingBankPairs (B : Finset (Finset V)) : Finset (Finset (Finset V)) :=
  (B.powersetCard 2).filter
    (fun S => ∃ Q ∈ S, ∃ T ∈ S, Q ≠ T ∧ (Q ∩ T).Nonempty)

theorem bank_vertex_card_le (B : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3) (a : V) :
    (B.filter (fun Q => a ∈ Q)).card ≤ Fintype.card V * L := by
  let W := univ.erase a
  have hSub : B.filter (fun Q => a ∈ Q) ⊆
      W.biUnion (fun b => B.filter (fun Q => a ∈ Q ∧ b ∈ Q)) := by
    intro Q hQ
    obtain ⟨hQB, haQ⟩ := mem_filter.mp hQ
    obtain ⟨b, hbQ, hba⟩ := exists_mem_ne (by rw [hB Q hQB]; norm_num : 1 < Q.card) a
    exact mem_biUnion.mpr ⟨b, mem_erase.mpr ⟨hba, mem_univ _⟩,
      mem_filter.mpr ⟨hQB, haQ, hbQ⟩⟩
  calc
    _ ≤ (W.biUnion (fun b => B.filter (fun Q => a ∈ Q ∧ b ∈ Q))).card := card_le_card hSub
    _ ≤ ∑ b ∈ W, (B.filter (fun Q => a ∈ Q ∧ b ∈ Q)).card := card_biUnion_le
    _ ≤ ∑ _b ∈ W, L := sum_le_sum (fun b hb => hL a b (mem_erase.mp hb).1.symm)
    _ = W.card * L := by simp
    _ ≤ _ := Nat.mul_le_mul_right L (card_le_univ W)

theorem touchingBank_card_le (B : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3) (T : Finset V) :
    (touchingBank B T).card ≤ T.card * Fintype.card V * L := by
  have hSub : touchingBank B T ⊆ T.biUnion (fun a => B.filter (fun Q => a ∈ Q)) := by
    intro Q hQ
    obtain ⟨hQB, a, ha⟩ := mem_filter.mp hQ
    obtain ⟨haQ, haT⟩ := mem_inter.mp ha
    exact mem_biUnion.mpr ⟨a, haT, mem_filter.mpr ⟨hQB, haQ⟩⟩
  calc
    _ ≤ (T.biUnion (fun a => B.filter (fun Q => a ∈ Q))).card := card_le_card hSub
    _ ≤ ∑ a ∈ T, (B.filter (fun Q => a ∈ Q)).card := card_biUnion_le
    _ ≤ ∑ _a ∈ T, Fintype.card V * L :=
      sum_le_sum (fun a _ => bank_vertex_card_le B L hL hB a)
    _ = _ := by simp [Nat.mul_assoc]

theorem overlappingBankPairs_card_le (B : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3) :
    (overlappingBankPairs B).card ≤ 3 * Fintype.card V * L * B.card := by
  have hSub : overlappingBankPairs B ⊆
      B.biUnion (fun Q => (touchingBank B Q).image (fun T => ({Q,T} : Finset (Finset V)))) := by
    intro S hS
    obtain ⟨hS, Q, hQ, T, hT, hQT, hInter⟩ := mem_filter.mp hS
    obtain ⟨hSB, hSCard⟩ := mem_powersetCard.mp hS
    have hPairSub : ({Q,T} : Finset (Finset V)) ⊆ S :=
      insert_subset_iff.mpr ⟨hQ, singleton_subset_iff.mpr hT⟩
    have hPairCard : ({Q,T} : Finset (Finset V)).card = 2 := by simp [hQT]
    have hPair : ({Q,T} : Finset (Finset V)) = S :=
      eq_of_subset_of_card_le hPairSub (by omega)
    have hTouch : T ∈ touchingBank B Q := by
      apply mem_filter.mpr
      exact ⟨hSB hT, by simpa only [inter_comm] using hInter⟩
    exact mem_biUnion.mpr ⟨Q, hSB hQ, mem_image.mpr ⟨T, hTouch, hPair⟩⟩
  calc
    _ ≤ (B.biUnion (fun Q => (touchingBank B Q).image (fun T => ({Q,T} : Finset (Finset V))))).card :=
      card_le_card hSub
    _ ≤ ∑ Q ∈ B, ((touchingBank B Q).image (fun T => ({Q,T} : Finset (Finset V)))).card := card_biUnion_le
    _ ≤ ∑ Q ∈ B, (touchingBank B Q).card := sum_le_sum (fun _ _ => card_image_le)
    _ ≤ ∑ _Q ∈ B, 3 * Fintype.card V * L := by
      apply sum_le_sum
      intro Q hQ
      simpa only [hB Q hQ] using touchingBank_card_le B L hL hB Q
    _ = _ := by simp [Nat.mul_comm]

#print axioms bank_vertex_card_le
#print axioms touchingBank_card_le
#print axioms overlappingBankPairs_card_le
end TypedTriangle.Pasch
