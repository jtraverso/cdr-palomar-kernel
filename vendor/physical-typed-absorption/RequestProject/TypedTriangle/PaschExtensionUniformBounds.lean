module
public import RequestProject.TypedTriangle.PaschExtensionMass
public import RequestProject.TypedTriangle.PaschUnrestrictedInfluence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem extensionMass_singleton_le (D : Finset (Finset V)) (μ : Finset V → ℝ)
    (Q : Finset V) (hQ : Q.card = 3) {b : ℝ} (hb : 0 ≤ b)
    (hμ0 : ∀ T ∈ D, 0 ≤ μ T) (hμb : ∀ T ∈ D, μ T ≤ b) :
    extensionMass D μ {Q} ≤ (Fintype.card V : ℝ)^3*b^3 := by
  have hBase := extensionMass_le_count_mul D μ {Q} hb hμ0 hμb
  have hFilter : (configurations D).filter (fun S => ({Q} : Finset (Finset V)) ⊆ S) =
      (configurations D).filter (fun S => Q ∈ S) := by
    ext S
    simp only [mem_filter,singleton_subset_iff]
  rw [hFilter,card_singleton] at hBase
  change extensionMass D μ {Q} ≤ (rootedCount D Q : ℝ)*b^3 at hBase
  have hCount : (rootedCount D Q : ℝ) ≤ (Fintype.card V : ℝ)^3 := by
    exact_mod_cast rootedCount_le_cube D Q hQ
  exact hBase.trans (mul_le_mul_of_nonneg_right hCount (pow_nonneg hb 3))

theorem extensionMass_singleton_le_diffuse (D : Finset (Finset V))
    (μ : Finset V → ℝ) (Q : Finset V) (hQ : Q.card = 3) {C : ℝ} (hC : 0 ≤ C)
    (hn : 0 < Fintype.card V) (hμ0 : ∀ T ∈ D, 0 ≤ μ T)
    (hμb : ∀ T ∈ D, μ T ≤ C/(Fintype.card V : ℝ)) :
    extensionMass D μ {Q} ≤ C^3 := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hh := extensionMass_singleton_le D μ Q hQ (div_nonneg hC hnR.le) hμ0 hμb
  apply hh.trans_eq
  field_simp

/-- Uniform conditional fractional degree for every nonempty partial Pasch.
All bounds are derived over the full triangle domain, without a packing premise. -/
theorem extensionMass_le_two_mul_cube (D : Finset (Finset V))
    (μ : Finset V → ℝ) (R : Finset (Finset V)) {C : ℝ}
    (hC : 1 ≤ C) (hn : 1 ≤ Fintype.card V)
    (hD : ∀ T ∈ D, T.card = 3) (hRD : R ⊆ D) (hR1 : 1 ≤ R.card) (hR4 : R.card ≤ 4)
    (hμ0 : ∀ T ∈ D, 0 ≤ μ T) (hμb : ∀ T ∈ D, μ T ≤ C/(Fintype.card V : ℝ)) :
    extensionMass D μ R ≤ 2*C^3 := by
  have hn0 : 0 < Fintype.card V := by omega
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < Fintype.card V := lt_of_lt_of_le zero_lt_one hnR
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hb : 0 ≤ C/(Fintype.card V : ℝ) := div_nonneg hC0 hnR0.le
  have hC23 : C^2 ≤ C^3 := by
    have hh := mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hC)
    nlinarith only [hh]
  have hC12 : C ≤ C^2 := by
    have hh := mul_nonneg hC0 (sub_nonneg.mpr hC)
    nlinarith only [hh]
  have hC3 : 0 ≤ C^3 := pow_nonneg hC0 3
  have hRatio : C/(Fintype.card V : ℝ) ≤ C := by
    apply (div_le_iff₀ hnR0).2
    have hh := mul_le_mul_of_nonneg_left hnR hC0
    simpa only [mul_one] using hh
  rcases (by omega : R.card = 1 ∨ R.card = 2 ∨ R.card = 3 ∨ R.card = 4) with hR | hR | hR | hR
  · obtain ⟨Q,rfl⟩ := card_eq_one.mp hR
    have hQ := hD Q (hRD (mem_singleton_self Q))
    have hh := extensionMass_singleton_le_diffuse D μ Q hQ hC0 hn0 hμ0 hμb
    exact hh.trans (by nlinarith only [hC3])
  · obtain ⟨Q,B,hQB,rfl⟩ := card_eq_two.mp hR
    have hh := extensionMass_pair_le_diffuse D μ Q B hQB hC0 hn0 hμ0 hμb
    have hDiv : 2*C^2/(Fintype.card V : ℝ) ≤ 2*C^2 := by
      apply (div_le_iff₀ hnR0).2
      have hMul := mul_le_mul_of_nonneg_left hnR (by positivity : 0 ≤ 2*C^2)
      simpa only [mul_one] using hMul
    exact hh.trans (hDiv.trans (by nlinarith only [hC23]))
  · have hh := extensionMass_triple_le D μ R hR hb hμ0 hμb
    exact hh.trans (hRatio.trans (by nlinarith only [hC12,hC23,hC3]))
  · have hh := extensionMass_four_le D μ R hR hb hμ0 hμb
    exact hh.trans (by nlinarith only [hC,hC12,hC23,hC3])

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.extensionMass_singleton_le
#print axioms TypedTriangle.Pasch.extensionMass_singleton_le_diffuse
#print axioms TypedTriangle.Pasch.extensionMass_le_two_mul_cube
