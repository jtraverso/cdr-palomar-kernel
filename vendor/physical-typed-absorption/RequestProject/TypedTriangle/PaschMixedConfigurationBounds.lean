module
public import RequestProject.TypedTriangle.PaschMixedMass
public import RequestProject.TypedTriangle.PaschBankConfigurationBounds
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V] [DecidableEq V]

def mixedConfigurations (A B : Finset (Finset V)) (ℓ : ℕ) (R : Finset (Finset V)) :=
  (configurations (A ∪ B)).filter (fun K => (K \ B).card = ℓ ∧ R ⊆ K \ B)

theorem outside_bank_subset {A B K : Finset (Finset V)}
    (hK : K ∈ configurations (A ∪ B)) : K \ B ⊆ A := by
  intro T hT
  obtain ⟨hTK, hTB⟩ := mem_sdiff.mp hT
  exact (mem_union.mp ((mem_configurations.mp hK).1 hTK)).resolve_right hTB

theorem mixedConfigurations_data {A B R K : Finset (Finset V)} {ℓ : ℕ}
    (hK : K ∈ mixedConfigurations A B ℓ R) :
    K ∈ configurations (A ∪ B) ∧ K \ B ⊆ A ∧ (K \ B).card = ℓ ∧ R ⊆ K \ B := by
  obtain ⟨hK, hCard, hR⟩ := mem_filter.mp hK
  exact ⟨hK, outside_bank_subset hK, hCard, hR⟩

theorem mixedConfigurations_bank_card {A B R K : Finset (Finset V)} {ℓ : ℕ}
    (hK : K ∈ mixedConfigurations A B ℓ R) : (K ∩ B).card = 4 - ℓ := by
  obtain ⟨hConf, _, hCard, _⟩ := mixedConfigurations_data hK
  have hk := (mem_configurations.mp hConf).2.1
  have hh := card_sdiff_add_card_inter K B
  omega

theorem mixedConfigurations_empty_of_bank_member {A B R : Finset (Finset V)} {ℓ : ℕ}
    {Q : Finset V} (hQR : Q ∈ R) (hQB : Q ∈ B) : mixedConfigurations A B ℓ R = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro K hK
  exact (mem_sdiff.mp ((mixedConfigurations_data hK).2.2.2 hQR)).2 hQB

theorem mixedDegree_eq_mixedConfigurations (A B : Finset (Finset V))
    (μ : Finset V → ℝ) (ℓ : ℕ) (R : Finset (Finset V)) :
    mixedDegree A B μ ℓ R =
      ∑ K ∈ mixedConfigurations A B ℓ R, ∏ T ∈ (K \ B) \ R, μ T := by
  rw [mixedDegree_eq_configuration_sum]
  apply sum_congr
  · ext K
    simp only [mixedConfigurations, mem_filter, mem_powersetCard]
    constructor
    · exact fun h => ⟨h.1, h.2.1.2, h.2.2⟩
    · exact fun h => ⟨h.1, ⟨outside_bank_subset h.1, h.2.1⟩, h.2.2⟩
  · intro K _
    rfl

theorem mixedDegree_le_card_power (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (ℓ : ℕ) (R : Finset (Finset V)) {b : ℝ} (hb : 0 ≤ b)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ b) :
    mixedDegree A B μ ℓ R ≤ ((mixedConfigurations A B ℓ R).card : ℝ) * b^(ℓ-R.card) := by
  rw [mixedDegree_eq_mixedConfigurations]
  exact outside_product_sum_le A B _ μ R ℓ hb
    (fun K hK => (mixedConfigurations_data hK).2) hμ0 hμb

theorem mixedMass_eq_mixedDegree_empty (A B : Finset (Finset V))
    (μ : Finset V → ℝ) (ℓ : ℕ) : mixedMass A B μ ℓ = mixedDegree A B μ ℓ ∅ := by
  simp [mixedMass, mixedDegree]

theorem mixedConfigurations_three_card_le (A B R : Finset (Finset V))
    (hB : ∀ Q ∈ B, Q.card = 3) :
    (mixedConfigurations A B 3 R).card ≤ (Fintype.card V)^3 * B.card := by
  have hSub : mixedConfigurations A B 3 R ⊆ bankNonemptyConfigurations (A ∪ B) B := by
    intro K hK
    have hd := mixedConfigurations_data hK
    have hc := mixedConfigurations_bank_card hK
    exact mem_filter.mpr ⟨hd.1, card_pos.mp (by omega)⟩
  exact (card_le_card hSub).trans (bankNonemptyConfigurations_card_le _ B hB)

theorem mixedConfigurations_two_card_le (A B R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3) :
    (mixedConfigurations A B 2 R).card ≤ 6*(Fintype.card V)^2*L*B.card := by
  have hSub : mixedConfigurations A B 2 R ⊆ bankTwoConfigurations (A ∪ B) B := by
    intro K hK
    have hd := mixedConfigurations_data hK
    have hc := mixedConfigurations_bank_card hK
    exact mem_filter.mpr ⟨hd.1, by omega⟩
  calc
    _ ≤ (bankTwoConfigurations (A ∪ B) B).card := card_le_card hSub
    _ ≤ 2*Fintype.card V*(overlappingBankPairs B).card := bankTwoConfigurations_card_le _ B
    _ ≤ 2*Fintype.card V*(3*Fintype.card V*L*B.card) :=
      Nat.mul_le_mul_left _ (overlappingBankPairs_card_le B L hL hB)
    _ = _ := by ring

theorem mixedConfigurations_one_card_le (A B R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3) :
    (mixedConfigurations A B 1 R).card ≤ 27*Fintype.card V*L^2*B.card := by
  have hSub : mixedConfigurations A B 1 R ⊆ bankTripleConfigurations (A ∪ B) B := by
    intro K hK
    have hd := mixedConfigurations_data hK
    have hc := mixedConfigurations_bank_card hK
    exact mem_filter.mpr ⟨hd.1, by omega⟩
  exact (card_le_card hSub).trans ((bankTripleConfigurations_card_le _ B).trans
    (compatibleOldTriples_card_le B L hL hB))

theorem mixedConfigurations_pair_card_le (A B R : Finset (Finset V)) (ℓ : ℕ)
    (hR : R.card = 2) : (mixedConfigurations A B ℓ R).card ≤ 2*Fintype.card V := by
  have hSub : mixedConfigurations A B ℓ R ⊆
      (configurations (A ∪ B)).filter (fun K => R ⊆ K) := by
    intro K hK
    have hd := mixedConfigurations_data hK
    exact mem_filter.mpr ⟨hd.1, hd.2.2.2.trans sdiff_subset⟩
  exact (card_le_card hSub).trans (configurations_containing_pair_card_le _ R hR)

theorem mixedConfigurations_triple_card_le (A B R : Finset (Finset V)) (ℓ : ℕ)
    (hR : R.card = 3) : (mixedConfigurations A B ℓ R).card ≤ 1 := by
  have hSub : mixedConfigurations A B ℓ R ⊆ tripleExtensions (A ∪ B) R := by
    intro K hK
    have hd := mixedConfigurations_data hK
    exact mem_filter.mpr ⟨hd.1, hd.2.2.2.trans sdiff_subset⟩
  exact (card_le_card hSub).trans (tripleExtensions_card_le _ R hR)

theorem mixedConfigurations_root_three_card_le (A B : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound B L) (hB : ∀ T ∈ B, T.card = 3)
    (Q : Finset V) (hQ : Q.card = 3) (hQB : Q ∉ B) :
    (mixedConfigurations A B 3 {Q}).card ≤ 6*(Fintype.card V)^2*L := by
  have hSub : mixedConfigurations A B 3 {Q} ⊆ bankTouchConfigurations (A ∪ B) B Q := by
    intro K hK
    have hd := mixedConfigurations_data hK
    have hc := mixedConfigurations_bank_card hK
    exact mem_filter.mpr ⟨hd.1, sdiff_subset (hd.2.2.2 (mem_singleton_self Q)), card_pos.mp (by omega)⟩
  calc
    _ ≤ (bankTouchConfigurations (A ∪ B) B Q).card := card_le_card hSub
    _ ≤ 2*Fintype.card V*(touchingBank B Q).card := bankTouchConfigurations_card_le _ B Q hQB
    _ ≤ 2*Fintype.card V*(Q.card*Fintype.card V*L) :=
      Nat.mul_le_mul_left _ (touchingBank_card_le B L hL hB Q)
    _ = _ := by rw [hQ]; ring

theorem mixedConfigurations_root_small_card_le (A B : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound B L) (hB : ∀ T ∈ B, T.card = 3)
    (Q : Finset V) (hQ : Q.card = 3) (hQB : Q ∉ B) (ℓ : ℕ) (hℓ : ℓ ≤ 2) :
    (mixedConfigurations A B ℓ {Q}).card ≤ 27*Fintype.card V*L^2 := by
  have hSub : mixedConfigurations A B ℓ {Q} ⊆ bankPairConfigurations (A ∪ B) B Q := by
    intro K hK
    have hd := mixedConfigurations_data hK
    have hc := mixedConfigurations_bank_card hK
    exact mem_filter.mpr ⟨hd.1, sdiff_subset (hd.2.2.2 (mem_singleton_self Q)), by omega⟩
  exact (card_le_card hSub).trans ((bankPairConfigurations_card_le _ B Q hQB).trans
    (compatibleOldPairsAround_card_le B L hL hB Q hQB hQ))

#print axioms mixedDegree_le_card_power
#print axioms mixedConfigurations_three_card_le
#print axioms mixedConfigurations_two_card_le
#print axioms mixedConfigurations_one_card_le
#print axioms mixedConfigurations_pair_card_le
#print axioms mixedConfigurations_triple_card_le
#print axioms mixedConfigurations_root_three_card_le
#print axioms mixedConfigurations_root_small_card_le
end TypedTriangle.Pasch
