module
public import RequestProject.TypedTriangle.PaschLocalMixedConfigurationBounds
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

theorem compatibleOldPairsAround_card_le_on_child (B : Finset (Finset V))
    (X : Finset V) (L : ℕ) (hL : PairCodegreeBound B L)
    (hB : ∀ T ∈ B, T.card = 3) (hBX : ∀ T ∈ B, 2 ≤ (T ∩ X).card)
    (Q : Finset V) (hQ : Q ∉ B) (hQc : Q.card = 3) :
    (compatibleOldPairsAround B Q).card ≤ 27*X.card*L^2 := by
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
  have hTouch : (touchingBank B Q).card ≤ 3*X.card*L := by
    simpa only [hQc] using touchingBank_card_le_on_child B X L hL hBX Q
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
    _ ≤ (3*X.card*L)*(9*L) := Nat.mul_le_mul_right _ hTouch
    _ = _ := by ring

theorem compatibleOldTriples_card_le_on_child (B : Finset (Finset V))
    (X : Finset V) (L : ℕ) (hL : PairCodegreeBound B L)
    (hB : ∀ T ∈ B, T.card = 3) (hBX : ∀ T ∈ B, 2 ≤ (T ∩ X).card) :
    (compatibleOldTriples B).card ≤ 27*X.card*L^2*B.card := by
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
    _ ≤ ∑ _Q ∈ B, 27*X.card*L^2 := by
      apply sum_le_sum
      intro Q hQ
      have hQc := hB Q hQ
      have hTouch : (touchingBank B Q).card ≤ 3*X.card*L := by
        simpa only [hQc] using touchingBank_card_le_on_child B X L hL hBX Q
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
        _ ≤ (3*X.card*L)*(9*L) := Nat.mul_le_mul_right _ hTouch
        _ = _ := by ring
    _ = _ := by simp [Nat.mul_comm]

variable [Fintype V]

theorem mixedConfigurations_one_card_le_on_child (A B R : Finset (Finset V))
    (X : Finset V) (L : ℕ) (hL : PairCodegreeBound B L)
    (hB : ∀ T ∈ B, T.card = 3) (hBX : ∀ T ∈ B, 2 ≤ (T ∩ X).card) :
    (mixedConfigurations A B 1 R).card ≤ 27*X.card*L^2*B.card := by
  have hSub : mixedConfigurations A B 1 R ⊆ bankTripleConfigurations (A ∪ B) B := by
    intro K hK
    have hd := mixedConfigurations_data hK
    have hc := mixedConfigurations_bank_card hK
    exact mem_filter.mpr ⟨hd.1,by omega⟩
  exact (card_le_card hSub).trans ((bankTripleConfigurations_card_le _ B).trans
    (compatibleOldTriples_card_le_on_child B X L hL hB hBX))

theorem mixedConfigurations_root_small_card_le_on_child (A B : Finset (Finset V))
    (X : Finset V) (L : ℕ) (hL : PairCodegreeBound B L)
    (hB : ∀ T ∈ B, T.card = 3) (hBX : ∀ T ∈ B, 2 ≤ (T ∩ X).card)
    (Q : Finset V) (hQ : Q.card = 3) (hQB : Q ∉ B) (ℓ : ℕ) (hℓ : ℓ ≤ 2) :
    (mixedConfigurations A B ℓ {Q}).card ≤ 27*X.card*L^2 := by
  have hSub : mixedConfigurations A B ℓ {Q} ⊆ bankPairConfigurations (A ∪ B) B Q := by
    intro K hK
    have hd := mixedConfigurations_data hK
    have hc := mixedConfigurations_bank_card hK
    exact mem_filter.mpr ⟨hd.1,sdiff_subset (hd.2.2.2 (mem_singleton_self Q)),by omega⟩
  exact (card_le_card hSub).trans ((bankPairConfigurations_card_le _ B Q hQB).trans
    (compatibleOldPairsAround_card_le_on_child B X L hL hB hBX Q hQB hQ))

theorem mixedMass_one_le_on_child (A B : Finset (Finset V)) (X : Finset V)
    (μ : Finset V → ℝ) (C : ℝ) (L : ℕ) (hC : 0 ≤ C) (hX : 0 < X.card)
    (hL : PairCodegreeBound B L) (hB : ∀ T ∈ B, T.card = 3)
    (hBX : ∀ T ∈ B, 2 ≤ (T ∩ X).card)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(X.card : ℝ)) :
    mixedMass A B μ 1 ≤ 27*C*(L : ℝ)^2*B.card := by
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hX
  rw [mixedMass_eq_mixedDegree_empty]
  have hh := mixedDegree_le_card_power A B μ 1 ∅ (div_nonneg hC hX0.le) hμ0 hμb
  have hCount : ((mixedConfigurations A B 1 ∅).card : ℝ) ≤ 27*(X.card : ℝ)*L^2*B.card := by
    exact_mod_cast mixedConfigurations_one_card_le_on_child A B ∅ X L hL hB hBX
  have hBound := hh.trans (mul_le_mul_of_nonneg_right hCount
    (pow_nonneg (div_nonneg hC hX0.le) (1-(∅ : Finset (Finset V)).card)))
  apply hBound.trans_eq
  simp only [card_empty, Nat.sub_zero, pow_one]
  field_simp [ne_of_gt hX0]
  <;> ring

#print axioms compatibleOldPairsAround_card_le_on_child
#print axioms compatibleOldTriples_card_le_on_child
#print axioms mixedConfigurations_one_card_le_on_child
#print axioms mixedConfigurations_root_small_card_le_on_child
#print axioms mixedMass_one_le_on_child
end TypedTriangle.Pasch
