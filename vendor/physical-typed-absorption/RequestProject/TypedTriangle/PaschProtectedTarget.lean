module
public import RequestProject.TypedTriangle.PaschFractionalReserve
public import RequestProject.TypedTriangle.PaschTargetUpper
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

def targetPaymentCost (C K : ℝ) : ℝ := 15*C*K*C^3/4+C^3

def targetPaymentBudget (C K σ : ℝ) : ℝ :=
  min (1/(C*(K+1))) (σ/(2*(targetPaymentCost C K+1)))

theorem targetPaymentCost_nonneg {C K : ℝ} (hC : 0 < C) (hK : 0 ≤ K) :
    0 ≤ targetPaymentCost C K := by unfold targetPaymentCost; positivity

theorem targetPaymentBudget_pos {C K σ : ℝ} (hC : 0 < C) (hK : 0 ≤ K) (hσ : 0 < σ) :
    0 < targetPaymentBudget C K σ := by
  have hB := targetPaymentCost_nonneg hC hK
  unfold targetPaymentBudget
  positivity

theorem targetPaymentBudget_bounds {C K σ : ℝ} (hC : 0 < C) (hK : 0 ≤ K) (hσ : 0 < σ) :
    C*(K*targetPaymentBudget C K σ) ≤ 1 ∧
      targetPaymentCost C K*targetPaymentBudget C K σ ≤ σ/2 := by
  let δ := targetPaymentBudget C K σ
  have hδ : 0 ≤ δ := (targetPaymentBudget_pos hC hK hσ).le
  have hB := targetPaymentCost_nonneg hC hK
  have hDen : 0 < C*(K+1) := by positivity
  have hCap : δ*(C*(K+1)) ≤ 1 :=
    (le_div_iff₀ hDen).mp (min_le_left _ _)
  have hCK : C*K ≤ C*(K+1) := by nlinarith only [hC]
  constructor
  · calc
      C*(K*δ) = (C*K)*δ := by ring
      _ ≤ (C*(K+1))*δ := mul_le_mul_of_nonneg_right hCK hδ
      _ ≤ 1 := by nlinarith only [hCap]
  · have hPaid : δ*(2*(targetPaymentCost C K+1)) ≤ σ :=
      (le_div_iff₀ (by positivity : 0 < 2*(targetPaymentCost C K+1))).mp (min_le_right _ _)
    nlinarith only [hPaid,hδ]

/-- Restricting the triangle domain decreases the nonnegative fractional
Pasch target. This concerns fractional targets, not arbitrary integral edits. -/
theorem target_mono_domain (D E : Finset (Finset V)) (μ : Finset V → ℝ)
    (hED : E ⊆ D) (hμ : ∀ T ∈ D, 0 ≤ μ T) : target μ E ≤ target μ D := by
  simp only [target,statistic_eq_sum]
  apply sum_le_sum_of_subset_of_nonneg
  · intro S hS
    obtain ⟨hSE,hCard,hPasch⟩ := mem_configurations.mp hS
    exact mem_configurations.mpr ⟨hSE.trans hED,hCard,hPasch⟩
  · intro S hS _
    exact prod_nonneg (fun T hT => hμ T ((mem_configurations.mp hS).1 hT))

omit [DecidableEq V] in
/-- Both changes of fractional target are paid: the exact residual seed
perturbation and removal of triangles meeting the reserved edge set. The
pointwise and degree premises are technical certificates from seed persistence. -/
theorem protected_target_transfer [Fintype V] {I : Type*}
    {H : Host V I} {F : Set (Multiset I)} {C : ℝ} {φ ψ : Finset V → ℝ}
    (hC : 0 < C) (hφ : IsDiffuseSeed H F C φ)
    (R : Finset (Sym2 V)) (hR : R ⊆ edges H) (K δ d : ℝ)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hd : d ≤ δ*Fintype.card V)
    (hSmall : C*(K*δ) ≤ 1)
    (hDegree : ∀ v, (degIn R v:ℝ) ≤ δ*Fintype.card V)
    (hClose : ∀ T, IsAllowed (residual H R) F T →
      |ψ T-φ T| ≤ K*d/(Fintype.card V:ℝ)^2)
    (hn : 0 < (Fintype.card V:ℝ)) :
    letI : DecidableEq V := Classical.decEq V
    |target ψ (allowed (residual H R) F)-target φ (allowed H F)| ≤
      targetPaymentCost C K*δ*(Fintype.card V:ℝ)^2 := by
  letI : DecidableEq V := Classical.decEq V
  let D := allowed H F
  let E := allowed (residual H R) F
  have hED : E ⊆ D := by
    intro T hT
    exact mem_filter.mpr ⟨mem_univ _,isAllowed_mono (subHost_le H _) rfl (isAllowed_of_mem_allowed hT)⟩
  have hφ0 : ∀ T ∈ D, 0 ≤ φ T := fun T hT =>
    (by positivity : (0:ℝ) ≤ 1/(C*Fintype.card V)).trans
      (hφ.1 T (isAllowed_of_mem_allowed hT)).1
  have hPert := target_difference_of_paid_seed E φ ψ (Fintype.card V) C K δ d hn hC hK hδ hd hSmall
    (fun T hT => (hφ.1 T (isAllowed_of_mem_allowed (hED hT))).1)
    (fun T hT => hClose T (isAllowed_of_mem_allowed hT))
  have hMono := target_mono_domain D E φ hED hφ0
  have hnNat : 0 < Fintype.card V := by exact_mod_cast hn
  have hUpper := hMono.trans (target_le_seed_order_square hC hφ hnNat)
  have hPert' := hPert.trans (mul_le_mul_of_nonneg_left hUpper (by positivity : 0 ≤ 15*(C*(K*δ))))
  have hLoss := reserve_target_loss_le_degree hC hφ R hR δ hDegree hn
  calc
    _ ≤ |target ψ E-target φ E|+|target φ E-target φ D| := abs_sub_le _ _ _
    _ ≤ 15*(C*(K*δ))*(C^3*(Fintype.card V:ℝ)^2/4)+C^3*(δ*(Fintype.card V:ℝ)^2) :=
      add_le_add hPert' (by simpa only [abs_sub_comm] using hLoss)
    _ = _ := by unfold targetPaymentCost; ring

#print axioms targetPaymentCost_nonneg
#print axioms targetPaymentBudget_pos
#print axioms targetPaymentBudget_bounds
#print axioms target_mono_domain
#print axioms protected_target_transfer
end TypedTriangle.Pasch
