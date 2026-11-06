module
public import RequestProject.TypedTriangle.PaschLocalBankCompatibility
public import RequestProject.TypedTriangle.PaschTwoNewCompletions
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

theorem IsPasch.blocks_inside_of_three_inside {K New : Finset (Finset V)}
    (hK : IsPasch K) (X : Finset V) (hNew : New ⊆ K) (hThree : 3 ≤ New.card)
    (hInside : ∀ T ∈ New, T ⊆ X) {T : Finset V} (hT : T ∈ K) : T ⊆ X := by
  intro v hv
  by_contra hvX
  have hvSupport : v ∈ K.biUnion id := mem_biUnion.mpr ⟨T,hT,hv⟩
  have hd := hK.2.2.2.1 v hvSupport
  have hSub : K.filter (fun Q => v ∈ Q) ⊆ K \ New := by
    intro Q hQ
    obtain ⟨hQK,hvQ⟩ := mem_filter.mp hQ
    exact mem_sdiff.mpr ⟨hQK,fun hQN => hvX (hInside Q hQN hvQ)⟩
  have hh := card_le_card hSub
  rw [hd,card_sdiff_of_subset hNew,hK.1] at hh
  omega

private theorem mem_localPairExtensions {D : Finset (Finset V)} {X Q B : Finset V}
    {K : Finset (Finset V)} :
    K ∈ localPairExtensions D X Q B ↔ K ∈ configurations D ∧ Q ∈ K ∧ B ∈ K ∧
      ∀ T ∈ K, T ≠ Q → T ≠ B → T ⊆ X := by
  simp only [localPairExtensions,pairExtensions,mem_filter,and_assoc]

variable [Fintype V]

theorem mixedConfigurations_three_inside {A B R K : Finset (Finset V)}
    (X : Finset V) (hA : ∀ T ∈ A, T ⊆ X)
    (hK : K ∈ mixedConfigurations A B 3 R) {T : Finset V} (hT : T ∈ K) : T ⊆ X := by
  obtain ⟨hConf,hOutside,hCard,hR⟩ := mixedConfigurations_data hK
  exact (mem_configurations.mp hConf).2.2.blocks_inside_of_three_inside X sdiff_subset
    (by omega) (fun Q hQ => hA Q (hOutside hQ)) hT

theorem mixedConfigurations_three_pair_card_le_on_child (A B R : Finset (Finset V))
    (X : Finset V) (hA : ∀ T ∈ A, T ⊆ X) (hR : R.card = 2) :
    (mixedConfigurations A B 3 R).card ≤ 2*X.card := by
  have hSub : mixedConfigurations A B 3 R ⊆ localPairFamily (A ∪ B) X R := by
    intro K hK
    have hd := mixedConfigurations_data hK
    apply mem_filter.mpr
    exact ⟨hd.1,hd.2.2.2.trans sdiff_subset,
      fun T hT _ => mixedConfigurations_three_inside X hA hK hT⟩
  exact (card_le_card hSub).trans (localPairFamily_card_le (A ∪ B) X R hR)

theorem mixedConfigurations_three_root_card_le_on_child (A B : Finset (Finset V))
    (X : Finset V) (L : ℕ) (hL : PairCodegreeBound B L)
    (hA : ∀ T ∈ A, T ⊆ X) (hBX : ∀ T ∈ B, 2 ≤ (T ∩ X).card)
    (Q : Finset V) (hQ : Q.card = 3) (hQB : Q ∉ B) :
    (mixedConfigurations A B 3 {Q}).card ≤ 6*X.card^2*L := by
  let E := (touchingBank B Q).biUnion (fun T => localPairExtensions (A ∪ B) X Q T)
  have hSub : mixedConfigurations A B 3 {Q} ⊆ E := by
    intro K hK
    have hd := mixedConfigurations_data hK
    have hc := mixedConfigurations_bank_card hK
    have hQK := sdiff_subset (hd.2.2.2 (mem_singleton_self Q))
    obtain ⟨T,hTKB⟩ := card_pos.mp (show 0 < (K ∩ B).card by omega)
    obtain ⟨hTK,hTB⟩ := mem_inter.mp hTKB
    have hQT : Q ≠ T := by rintro rfl; exact hQB hTB
    have hTouch : T ∈ touchingBank B Q := mem_filter.mpr
      ⟨hTB,inter_nonempty (mem_configurations.mp hd.1).2.2 hTK hQK hQT.symm⟩
    apply mem_biUnion.mpr
    refine ⟨T,hTouch,mem_localPairExtensions.mpr ⟨hd.1,hQK,hTK,?_⟩⟩
    intro U hUK _ _
    exact mixedConfigurations_three_inside X hA hK hUK
  have hTouch : (touchingBank B Q).card ≤ 3*X.card*L := by
    simpa only [hQ] using touchingBank_card_le_on_child B X L hL hBX Q
  calc
    _ ≤ E.card := card_le_card hSub
    _ ≤ ∑ T ∈ touchingBank B Q, (localPairExtensions (A ∪ B) X Q T).card := card_biUnion_le
    _ ≤ ∑ _T ∈ touchingBank B Q, 2*X.card := by
      apply sum_le_sum
      intro T hT
      have hQT : Q ≠ T := by rintro rfl; exact hQB (mem_filter.mp hT).1
      exact localPairExtensions_card_le (A ∪ B) X Q T hQT
    _ = (touchingBank B Q).card*(2*X.card) := by simp
    _ ≤ (3*X.card*L)*(2*X.card) := Nat.mul_le_mul_right _ hTouch
    _ = _ := by ring

theorem mixedDegree_at_arity (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (R : Finset (Finset V)) (hRA : R ⊆ A) :
    mixedDegree A B μ R.card R = completionWeight B R := by
  have hFilter : (A.powersetCard R.card).filter (fun S => R ⊆ S) = {R} := by
    ext S
    simp only [mem_filter,mem_powersetCard,mem_singleton]
    constructor
    · rintro ⟨⟨hSA,hSc⟩,hRS⟩
      exact (eq_of_subset_of_card_le hRS (by omega)).symm
    · rintro rfl
      exact ⟨⟨hRA,rfl⟩,subset_rfl⟩
  rw [mixedDegree,hFilter,sum_singleton,sdiff_self]
  simp only [bot_eq_empty,prod_empty,mul_one]

theorem mixedDegree_two_pair_le_codegree (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (L : ℕ) (hL : PairCodegreeBound B L) (R : Finset (Finset V))
    (hRA : R ⊆ A) (hR : R.card = 2) : mixedDegree A B μ 2 R ≤ 9*(L : ℝ) := by
  have he := mixedDegree_at_arity A B μ R hRA
  rw [hR] at he
  rw [he]
  change (completionCount B R : ℝ) ≤ 9*(L : ℝ)
  exact_mod_cast completionCount_two_le hL R hR

theorem mixedDegree_three_triple_le_one (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (R : Finset (Finset V)) (hRA : R ⊆ A) (hR : R.card = 3) :
    mixedDegree A B μ 3 R ≤ 1 := by
  have he := mixedDegree_at_arity A B μ R hRA
  rw [hR] at he
  rw [he]
  change (completionCount B R : ℝ) ≤ 1
  exact_mod_cast completionCount_three_le B R hR

theorem mixedDegree_le_child_nat_bound (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (X : Finset V) (ℓ : ℕ) (R : Finset (Finset V)) (C : ℝ) (hC : 0 ≤ C)
    (hX : 0 < X.card) (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(X.card : ℝ))
    (M : ℕ) (hM : (mixedConfigurations A B ℓ R).card ≤ M) :
    mixedDegree A B μ ℓ R ≤ (M : ℝ)*(C/(X.card : ℝ))^(ℓ-R.card) := by
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hX
  have hb := div_nonneg hC hX0.le
  have hh := mixedDegree_le_card_power A B μ ℓ R hb hμ0 hμb
  have hCount : ((mixedConfigurations A B ℓ R).card : ℝ) ≤ M := by exact_mod_cast hM
  exact hh.trans (mul_le_mul_of_nonneg_right hCount (pow_nonneg hb _))

theorem mixedDegree_one_root_le_on_child (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (X : Finset V) (C : ℝ) (L : ℕ) (hC : 0 ≤ C) (hX : 0 < X.card)
    (hL : PairCodegreeBound B L) (hB : ∀ T ∈ B, T.card = 3)
    (hBX : ∀ T ∈ B, 2 ≤ (T ∩ X).card)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(X.card : ℝ))
    (Q : Finset V) (hQ : Q.card = 3) (hQB : Q ∉ B) :
    mixedDegree A B μ 1 {Q} ≤ 27*(X.card : ℝ)*(L : ℝ)^2 := by
  have hh := mixedDegree_le_child_nat_bound A B μ X 1 {Q} C hC hX hμ0 hμb
    (27*X.card*L^2)
    (mixedConfigurations_root_small_card_le_on_child A B X L hL hB hBX Q hQ hQB 1 (by omega))
  simpa only [card_singleton,Nat.sub_self,pow_zero,mul_one,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hh

theorem mixedDegree_two_root_le_on_child (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (X : Finset V) (C : ℝ) (L : ℕ) (hC : 0 ≤ C) (hX : 0 < X.card)
    (hL : PairCodegreeBound B L) (hB : ∀ T ∈ B, T.card = 3)
    (hBX : ∀ T ∈ B, 2 ≤ (T ∩ X).card)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(X.card : ℝ))
    (Q : Finset V) (hQ : Q.card = 3) (hQB : Q ∉ B) :
    mixedDegree A B μ 2 {Q} ≤ 27*C*(L : ℝ)^2 := by
  have hh := mixedDegree_le_child_nat_bound A B μ X 2 {Q} C hC hX hμ0 hμb
    (27*X.card*L^2)
    (mixedConfigurations_root_small_card_le_on_child A B X L hL hB hBX Q hQ hQB 2 (by omega))
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hX
  apply hh.trans_eq
  simp only [card_singleton,Nat.reduceSub,pow_one,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  field_simp [ne_of_gt hX0]
  <;> ring

theorem mixedDegree_three_root_le_on_child (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (X : Finset V) (C : ℝ) (L : ℕ) (hC : 0 ≤ C) (hX : 0 < X.card)
    (hL : PairCodegreeBound B L) (hA : ∀ T ∈ A, T ⊆ X)
    (hBX : ∀ T ∈ B, 2 ≤ (T ∩ X).card)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(X.card : ℝ))
    (Q : Finset V) (hQ : Q.card = 3) (hQB : Q ∉ B) :
    mixedDegree A B μ 3 {Q} ≤ 6*(L : ℝ)*C^2 := by
  have hh := mixedDegree_le_child_nat_bound A B μ X 3 {Q} C hC hX hμ0 hμb
    (6*X.card^2*L)
    (mixedConfigurations_three_root_card_le_on_child A B X L hL hA hBX Q hQ hQB)
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hX
  apply hh.trans_eq
  simp only [card_singleton,Nat.reduceSub,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  field_simp [ne_of_gt hX0]
  <;> ring

theorem mixedDegree_three_pair_le_on_child (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (X : Finset V) (C : ℝ) (hC : 0 ≤ C) (hX : 0 < X.card)
    (hA : ∀ T ∈ A, T ⊆ X) (hμ0 : ∀ T ∈ A, 0 ≤ μ T)
    (hμb : ∀ T ∈ A, μ T ≤ C/(X.card : ℝ))
    (R : Finset (Finset V)) (hR : R.card = 2) :
    mixedDegree A B μ 3 R ≤ 2*C := by
  have hh := mixedDegree_le_child_nat_bound A B μ X 3 R C hC hX hμ0 hμb
    (2*X.card) (mixedConfigurations_three_pair_card_le_on_child A B R X hA hR)
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hX
  apply hh.trans_eq
  simp only [hR,Nat.reduceSub,pow_one,Nat.cast_mul,Nat.cast_ofNat]
  field_simp [ne_of_gt hX0]
  <;> ring

#print axioms IsPasch.blocks_inside_of_three_inside
#print axioms mixedConfigurations_three_inside
#print axioms mixedConfigurations_three_pair_card_le_on_child
#print axioms mixedConfigurations_three_root_card_le_on_child
#print axioms mixedDegree_at_arity
#print axioms mixedDegree_two_pair_le_codegree
#print axioms mixedDegree_three_triple_le_one
#print axioms mixedDegree_one_root_le_on_child
#print axioms mixedDegree_two_root_le_on_child
#print axioms mixedDegree_three_root_le_on_child
#print axioms mixedDegree_three_pair_le_on_child
end TypedTriangle.Pasch
