module
public import RequestProject.TypedTriangle.PaschBankIncidence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

/-- An exceptional old block contains two child vertices, so its incidence
at any ambient vertex is paid using child vertices, not the ambient order. -/
theorem bank_vertex_card_le_on_child (B : Finset (Finset V)) (X : Finset V) (L : ℕ)
    (hL : PairCodegreeBound B L) (hBX : ∀ Q ∈ B, 2 ≤ (Q ∩ X).card) (a : V) :
    (B.filter (fun Q => a ∈ Q)).card ≤ X.card*L := by
  let W := X.erase a
  have hSub : B.filter (fun Q => a ∈ Q) ⊆
      W.biUnion (fun b => B.filter (fun Q => a ∈ Q ∧ b ∈ Q)) := by
    intro Q hQ
    obtain ⟨hQB, haQ⟩ := mem_filter.mp hQ
    obtain ⟨b, hb, hba⟩ := exists_mem_ne (by have hh := hBX Q hQB; omega : 1 < (Q ∩ X).card) a
    exact mem_biUnion.mpr ⟨b, mem_erase.mpr ⟨hba, (mem_inter.mp hb).2⟩,
      mem_filter.mpr ⟨hQB, haQ, (mem_inter.mp hb).1⟩⟩
  calc
    _ ≤ (W.biUnion (fun b => B.filter (fun Q => a ∈ Q ∧ b ∈ Q))).card := card_le_card hSub
    _ ≤ ∑ b ∈ W, (B.filter (fun Q => a ∈ Q ∧ b ∈ Q)).card := card_biUnion_le
    _ ≤ ∑ _b ∈ W, L := sum_le_sum (fun b hb => hL a b (mem_erase.mp hb).1.symm)
    _ = W.card*L := by simp
    _ ≤ X.card*L := Nat.mul_le_mul_right L (card_le_card (erase_subset _ _))

theorem touchingBank_card_le_on_child (B : Finset (Finset V)) (X : Finset V) (L : ℕ)
    (hL : PairCodegreeBound B L) (hBX : ∀ Q ∈ B, 2 ≤ (Q ∩ X).card) (T : Finset V) :
    (touchingBank B T).card ≤ T.card*X.card*L := by
  have hSub : touchingBank B T ⊆ T.biUnion (fun a => B.filter (fun Q => a ∈ Q)) := by
    intro Q hQ
    obtain ⟨hQB, a, ha⟩ := mem_filter.mp hQ
    obtain ⟨haQ, haT⟩ := mem_inter.mp ha
    exact mem_biUnion.mpr ⟨a, haT, mem_filter.mpr ⟨hQB, haQ⟩⟩
  calc
    _ ≤ (T.biUnion (fun a => B.filter (fun Q => a ∈ Q))).card := card_le_card hSub
    _ ≤ ∑ a ∈ T, (B.filter (fun Q => a ∈ Q)).card := card_biUnion_le
    _ ≤ ∑ _a ∈ T, X.card*L :=
      sum_le_sum (fun a _ => bank_vertex_card_le_on_child B X L hL hBX a)
    _ = _ := by simp [Nat.mul_assoc]

theorem overlappingBankPairs_card_le_on_child (B : Finset (Finset V)) (X : Finset V)
    (L : ℕ) (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3)
    (hBX : ∀ Q ∈ B, 2 ≤ (Q ∩ X).card) :
    (overlappingBankPairs B).card ≤ 3*X.card*L*B.card := by
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
    _ ≤ ∑ _Q ∈ B, 3*X.card*L := by
      apply sum_le_sum
      intro Q hQ
      simpa only [hB Q hQ] using touchingBank_card_le_on_child B X L hL hBX Q
    _ = _ := by simp [Nat.mul_comm]

#print axioms bank_vertex_card_le_on_child
#print axioms touchingBank_card_le_on_child
#print axioms overlappingBankPairs_card_le_on_child
end TypedTriangle.Pasch
