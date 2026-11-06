module
public import RequestProject.TypedTriangle.PaschLocalBankIncidence
public import RequestProject.TypedTriangle.PaschLocalExtensionCounts
public import RequestProject.TypedTriangle.PaschMixedConfigurationBounds
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch

private theorem mem_localRootedConfigurations {U : Type*} [DecidableEq U]
    {D : Finset (Finset U)} {X Q : Finset U} {K : Finset (Finset U)} :
    K ∈ localRootedConfigurations D X Q ↔
      K ∈ configurations D ∧ Q ∈ K ∧ ∀ T ∈ K, T ≠ Q → T ⊆ X := by
  exact mem_filter

variable {V : Type*} [Fintype V] [DecidableEq V]

def localPairFamily (D : Finset (Finset V)) (X : Finset V) (P : Finset (Finset V)) :=
  (configurations D).filter (fun K => P ⊆ K ∧ ∀ T ∈ K, T ∉ P → T ⊆ X)

theorem localPairFamily_card_le (D : Finset (Finset V)) (X : Finset V)
    (P : Finset (Finset V)) (hP : P.card = 2) : (localPairFamily D X P).card ≤ 2*X.card := by
  obtain ⟨Q,T,hQT,rfl⟩ := card_eq_two.mp hP
  have he : localPairFamily D X {Q,T} = localPairExtensions D X Q T := by
    ext K
    simp only [localPairFamily, localPairExtensions, pairExtensions, mem_filter,
      insert_subset_iff, singleton_subset_iff, mem_insert, mem_singleton,
      not_or, and_imp, and_assoc]
  rw [he]
  exact localPairExtensions_card_le D X Q T hQT

theorem mixedConfigurations_three_card_le_on_child (A B R : Finset (Finset V))
    (X : Finset V) (hA : ∀ T ∈ A, T ⊆ X) (hB : ∀ T ∈ B, T.card = 3) :
    (mixedConfigurations A B 3 R).card ≤ X.card^3*B.card := by
  let E := B.biUnion (fun Q => localRootedConfigurations (A ∪ B) X Q)
  have hSub : mixedConfigurations A B 3 R ⊆ E := by
    intro K hK
    obtain ⟨hConf,hOutside,hCard,hR⟩ := mixedConfigurations_data hK
    have hc := mixedConfigurations_bank_card hK
    obtain ⟨Q,hQeq⟩ := card_eq_one.mp (show (K ∩ B).card = 1 by omega)
    have hQinter : Q ∈ K ∩ B := by rw [hQeq]; simp
    have hQK := (mem_inter.mp hQinter).1
    have hQB := (mem_inter.mp hQinter).2
    apply mem_biUnion.mpr
    refine ⟨Q,hQB,mem_localRootedConfigurations.mpr ⟨hConf,hQK,?_⟩⟩
    intro T hTK hTQ
    have hTB : T ∉ B := by
      intro hTB
      have hh : T ∈ K ∩ B := mem_inter.mpr ⟨hTK,hTB⟩
      rw [hQeq] at hh
      exact hTQ (mem_singleton.mp hh)
    exact hA T (hOutside (mem_sdiff.mpr ⟨hTK,hTB⟩))
  calc
    _ ≤ E.card := card_le_card hSub
    _ ≤ ∑ Q ∈ B, (localRootedConfigurations (A ∪ B) X Q).card := card_biUnion_le
    _ ≤ ∑ _Q ∈ B, X.card^3 := sum_le_sum (fun Q hQ =>
      localRootedConfigurations_card_le_cube (A ∪ B) X Q (hB Q hQ))
    _ = _ := by simp [Nat.mul_comm]

theorem mixedConfigurations_two_card_le_on_child (A B R : Finset (Finset V))
    (X : Finset V) (L : ℕ) (hL : PairCodegreeBound B L)
    (hA : ∀ T ∈ A, T ⊆ X) (hB : ∀ T ∈ B, T.card = 3)
    (hBX : ∀ T ∈ B, 2 ≤ (T ∩ X).card) :
    (mixedConfigurations A B 2 R).card ≤ 6*X.card^2*L*B.card := by
  let E := (overlappingBankPairs B).biUnion (fun P => localPairFamily (A ∪ B) X P)
  have hSub : mixedConfigurations A B 2 R ⊆ E := by
    intro K hK
    obtain ⟨hConf,hOutside,hCard,hR⟩ := mixedConfigurations_data hK
    have hPasch := (mem_configurations.mp hConf).2.2
    have hc : (K ∩ B).card = 2 := by have hh := mixedConfigurations_bank_card hK; omega
    have hP : K ∩ B ∈ overlappingBankPairs B := by
      obtain ⟨Q,T,hQT,hPair⟩ := card_eq_two.mp hc
      have hQP : Q ∈ K ∩ B := by rw [hPair]; simp
      have hTP : T ∈ K ∩ B := by rw [hPair]; simp
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨inter_subset_right,hc⟩,
        Q,hQP,T,hTP,hQT,inter_nonempty hPasch (mem_inter.mp hQP).1 (mem_inter.mp hTP).1 hQT⟩
    apply mem_biUnion.mpr
    refine ⟨K ∩ B,hP,mem_filter.mpr ⟨hConf,inter_subset_left,?_⟩⟩
    intro T hTK hTP
    have hTB : T ∉ B := fun hTB => hTP (mem_inter.mpr ⟨hTK,hTB⟩)
    exact hA T (hOutside (mem_sdiff.mpr ⟨hTK,hTB⟩))
  calc
    _ ≤ E.card := card_le_card hSub
    _ ≤ ∑ P ∈ overlappingBankPairs B, (localPairFamily (A ∪ B) X P).card := card_biUnion_le
    _ ≤ ∑ _P ∈ overlappingBankPairs B, 2*X.card := by
      apply sum_le_sum
      intro P hP
      exact localPairFamily_card_le (A ∪ B) X P (mem_powersetCard.mp (mem_filter.mp hP).1).2
    _ = 2*X.card*(overlappingBankPairs B).card := by simp [Nat.mul_comm]
    _ ≤ 2*X.card*(3*X.card*L*B.card) :=
      Nat.mul_le_mul_left _ (overlappingBankPairs_card_le_on_child B X L hL hB hBX)
    _ = _ := by ring

/-- Localizing before multiplying by diffuse coefficients removes all
parent/child ratio factors from the two-new-block mixed mass. -/
theorem mixedMass_two_le_on_child (A B : Finset (Finset V)) (X : Finset V)
    (μ : Finset V → ℝ) (C : ℝ) (L : ℕ) (hC : 0 ≤ C) (hX : 0 < X.card)
    (hL : PairCodegreeBound B L) (hA : ∀ T ∈ A, T ⊆ X)
    (hB : ∀ T ∈ B, T.card = 3) (hBX : ∀ T ∈ B, 2 ≤ (T ∩ X).card)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(X.card : ℝ)) :
    mixedMass A B μ 2 ≤ 6*(L : ℝ)*C^2*B.card := by
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hX
  rw [mixedMass_eq_mixedDegree_empty]
  have hh := mixedDegree_le_card_power A B μ 2 ∅ (div_nonneg hC hX0.le) hμ0 hμb
  have hCount : ((mixedConfigurations A B 2 ∅).card : ℝ) ≤ 6*(X.card : ℝ)^2*L*B.card := by
    exact_mod_cast mixedConfigurations_two_card_le_on_child A B ∅ X L hL hA hB hBX
  have hBound := hh.trans (mul_le_mul_of_nonneg_right hCount
    (pow_nonneg (div_nonneg hC hX0.le) (2-(∅ : Finset (Finset V)).card)))
  apply hBound.trans_eq
  simp only [card_empty, Nat.sub_zero]
  field_simp [ne_of_gt hX0]
  <;> ring

theorem mixedMass_three_le_on_child (A B : Finset (Finset V)) (X : Finset V)
    (μ : Finset V → ℝ) (C : ℝ) (hC : 0 ≤ C) (hX : 0 < X.card)
    (hA : ∀ T ∈ A, T ⊆ X) (hB : ∀ T ∈ B, T.card = 3)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(X.card : ℝ)) :
    mixedMass A B μ 3 ≤ C^3*B.card := by
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hX
  rw [mixedMass_eq_mixedDegree_empty]
  have hh := mixedDegree_le_card_power A B μ 3 ∅ (div_nonneg hC hX0.le) hμ0 hμb
  have hCount : ((mixedConfigurations A B 3 ∅).card : ℝ) ≤ (X.card : ℝ)^3*B.card := by
    exact_mod_cast mixedConfigurations_three_card_le_on_child A B ∅ X hA hB
  have hBound := hh.trans (mul_le_mul_of_nonneg_right hCount
    (pow_nonneg (div_nonneg hC hX0.le) (3-(∅ : Finset (Finset V)).card)))
  apply hBound.trans_eq
  simp only [card_empty, Nat.sub_zero]
  field_simp [ne_of_gt hX0]
  <;> ring

#print axioms localPairFamily_card_le
#print axioms mixedConfigurations_three_card_le_on_child
#print axioms mixedConfigurations_two_card_le_on_child
#print axioms mixedMass_two_le_on_child
#print axioms mixedMass_three_le_on_child
end TypedTriangle.Pasch
