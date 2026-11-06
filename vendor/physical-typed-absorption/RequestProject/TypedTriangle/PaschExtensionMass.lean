module
public import RequestProject.TypedTriangle.PaschPairExtensionBounds
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

/-- Fractional extension degree with the weights of the fixed blocks omitted. -/
def extensionMass (D : Finset (Finset V)) (μ : Finset V → ℝ)
    (R : Finset (Finset V)) : ℝ :=
  ∑ S ∈ (configurations D).filter (fun S => R ⊆ S), ∏ T ∈ S\R, μ T

theorem extensionMass_le_count_mul (D : Finset (Finset V))
    (μ : Finset V → ℝ) (R : Finset (Finset V)) {b : ℝ} (hb : 0 ≤ b)
    (hμ0 : ∀ T ∈ D, 0 ≤ μ T) (hμb : ∀ T ∈ D, μ T ≤ b) :
    extensionMass D μ R ≤
      (((configurations D).filter (fun S => R ⊆ S)).card : ℝ)*b^(4-R.card) := by
  unfold extensionMass
  calc
    (∑ S ∈ (configurations D).filter (fun S => R ⊆ S), ∏ T ∈ S\R, μ T) ≤
        ∑ S ∈ (configurations D).filter (fun S => R ⊆ S), b^(4-R.card) := by
      apply sum_le_sum
      intro S hS
      obtain ⟨hConf,hRS⟩ := mem_filter.mp hS
      have hSD := (mem_configurations.mp hConf).1
      have hCard := (mem_configurations.mp hConf).2.1
      have hh := prod_le_prod₀
        (fun T (hT : T ∈ S\R) => hμ0 T (hSD (mem_sdiff.mp hT).1))
        (fun T (hT : T ∈ S\R) => hμb T (hSD (mem_sdiff.mp hT).1))
      simpa only [prod_const,card_sdiff_of_subset hRS,hCard] using hh
    _ = _ := by rw [sum_const,nsmul_eq_mul]

theorem extensionMass_pair_le [Fintype V] (D : Finset (Finset V))
    (μ : Finset V → ℝ) (Q B : Finset V) (hQB : Q ≠ B) {b : ℝ} (hb : 0 ≤ b)
    (hμ0 : ∀ T ∈ D, 0 ≤ μ T) (hμb : ∀ T ∈ D, μ T ≤ b) :
    extensionMass D μ {Q,B} ≤ (2*(Fintype.card V : ℝ))*b^2 := by
  have hFilter : (configurations D).filter (fun S => ({Q,B} : Finset (Finset V)) ⊆ S) =
      pairExtensions D Q B := by
    ext S
    simp only [pairExtensions,mem_filter,insert_subset_iff,singleton_subset_iff]
  have hBase := extensionMass_le_count_mul D μ {Q,B} hb hμ0 hμb
  have hCard : ({Q,B} : Finset (Finset V)).card = 2 := by simp [hQB]
  rw [hFilter,hCard] at hBase
  have hCount : ((pairExtensions D Q B).card : ℝ) ≤ 2*(Fintype.card V : ℝ) := by
    exact_mod_cast pairExtensions_card_le D Q B hQB
  exact hBase.trans (mul_le_mul_of_nonneg_right hCount (sq_nonneg b))

theorem extensionMass_triple_le (D : Finset (Finset V))
    (μ : Finset V → ℝ) (K : Finset (Finset V)) (hK : K.card = 3) {b : ℝ} (hb : 0 ≤ b)
    (hμ0 : ∀ T ∈ D, 0 ≤ μ T) (hμb : ∀ T ∈ D, μ T ≤ b) :
    extensionMass D μ K ≤ b := by
  have hBase := extensionMass_le_count_mul D μ K hb hμ0 hμb
  have hCount : ((tripleExtensions D K).card : ℝ) ≤ 1 := by
    exact_mod_cast tripleExtensions_card_le D K hK
  change extensionMass D μ K ≤ ((tripleExtensions D K).card : ℝ)*b^(4-K.card) at hBase
  rw [hK] at hBase
  norm_num only [Nat.reduceSub,pow_one] at hBase
  exact hBase.trans ((mul_le_mul_of_nonneg_right hCount hb).trans_eq (one_mul b))

theorem extensionMass_pair_le_diffuse [Fintype V] (D : Finset (Finset V))
    (μ : Finset V → ℝ) (Q B : Finset V) (hQB : Q ≠ B) {C : ℝ} (hC : 0 ≤ C)
    (hn : 0 < Fintype.card V) (hμ0 : ∀ T ∈ D, 0 ≤ μ T)
    (hμb : ∀ T ∈ D, μ T ≤ C/(Fintype.card V : ℝ)) :
    extensionMass D μ {Q,B} ≤ 2*C^2/(Fintype.card V : ℝ) := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hh := extensionMass_pair_le D μ Q B hQB (div_nonneg hC hnR.le) hμ0 hμb
  apply hh.trans_eq
  field_simp
  <;> ring

theorem extensionMass_four_le (D : Finset (Finset V))
    (μ : Finset V → ℝ) (K : Finset (Finset V)) (hK : K.card = 4) {b : ℝ} (hb : 0 ≤ b)
    (hμ0 : ∀ T ∈ D, 0 ≤ μ T) (hμb : ∀ T ∈ D, μ T ≤ b) :
    extensionMass D μ K ≤ 1 := by
  have hBase := extensionMass_le_count_mul D μ K hb hμ0 hμb
  rw [hK] at hBase
  norm_num only [Nat.reduceSub,pow_zero,mul_one] at hBase
  have hCount : ((configurations D).filter (fun S => K ⊆ S)).card ≤ 1 := by
    apply card_le_one.mpr
    intro S hS T hT
    obtain ⟨hS,hKS⟩ := mem_filter.mp hS
    obtain ⟨hT,hKT⟩ := mem_filter.mp hT
    have hSC := (mem_configurations.mp hS).2.1
    have hTC := (mem_configurations.mp hT).2.1
    have hSK : K = S := eq_of_subset_of_card_le hKS (by omega)
    have hTK : K = T := eq_of_subset_of_card_le hKT (by omega)
    exact hSK.symm.trans hTK
  have hCountR : ((((configurations D).filter (fun S => K ⊆ S)).card : ℕ) : ℝ) ≤ 1 :=
    by exact_mod_cast hCount
  exact hBase.trans hCountR

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.extensionMass_le_count_mul
#print axioms TypedTriangle.Pasch.extensionMass_pair_le
#print axioms TypedTriangle.Pasch.extensionMass_triple_le
#print axioms TypedTriangle.Pasch.extensionMass_pair_le_diffuse
#print axioms TypedTriangle.Pasch.extensionMass_four_le
