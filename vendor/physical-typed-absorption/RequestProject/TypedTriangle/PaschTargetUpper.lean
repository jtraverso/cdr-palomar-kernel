module
public import RequestProject.TypedTriangle.PaschMarginals
public import RequestProject.TypedTriangle.PaschExtensionUniformBounds
public import RequestProject.TypedTriangle.SeedMassScale
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem target_le_cube_times_seed_mass (D : Finset (Finset V)) (μ : Finset V → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hn : 0 < Fintype.card V)
    (hD : ∀ T ∈ D, T.card = 3) (hμ0 : ∀ T ∈ D, 0 ≤ μ T)
    (hμb : ∀ T ∈ D, μ T ≤ C / (Fintype.card V : ℝ)) :
    target μ D ≤ C ^ 3 * (∑ T ∈ D, μ T) / 4 := by
  have hid := extensionMass_integrated D μ 1
  rw [powersetCard_one, sum_map] at hid
  simp only [Function.Embedding.coeFn_mk, prod_singleton] at hid
  simp only [Nat.choose_one_right, Nat.cast_ofNat] at hid
  have hsum : (∑ Q ∈ D, extensionMass D μ {Q} * μ Q) ≤ C ^ 3 * ∑ Q ∈ D, μ Q := by
    rw [mul_sum]
    apply sum_le_sum
    intro Q hQ
    exact mul_le_mul_of_nonneg_right
      (extensionMass_singleton_le_diffuse D μ Q (hD Q hQ) hC hn hμ0 hμb) (hμ0 Q hQ)
  linarith only [hid, hsum]

omit [DecidableEq V] in
theorem target_le_seed_order_square {I : Type*} {H : Host V I} {F : Set (Multiset I)}
    {C : ℝ} {μ : Finset V → ℝ} (hC : 0 < C) (hSeed : IsDiffuseSeed H F C μ)
    (hn : 0 < Fintype.card V) :
    letI : DecidableEq V := Classical.decEq V
    target μ (allowed H F) ≤ C ^ 3 * (Fintype.card V : ℝ) ^ 2 / 4 := by
  letI : DecidableEq V := Classical.decEq V
  have hμ0 : ∀ T ∈ allowed H F, 0 ≤ μ T := by
    intro T hT
    exact (by positivity : (0 : ℝ) ≤ 1 / (C * Fintype.card V)).trans
      (hSeed.1 T (isAllowed_of_mem_allowed hT)).1
  have hμb : ∀ T ∈ allowed H F, μ T ≤ C / (Fintype.card V : ℝ) :=
    fun T hT => (hSeed.1 T (isAllowed_of_mem_allowed hT)).2
  have hh := target_le_cube_times_seed_mass (allowed H F) μ hC.le hn
    (fun T hT => (isAllowed_of_mem_allowed hT).1) hμ0 hμb
  have hmass := (LocalizedCover.seed_total_mass_cap hSeed).2
  have hbound := mul_le_mul_of_nonneg_left hmass (pow_nonneg hC.le 3)
  linarith only [hh, hbound]

#print axioms target_le_cube_times_seed_mass
#print axioms target_le_seed_order_square
end TypedTriangle.Pasch
