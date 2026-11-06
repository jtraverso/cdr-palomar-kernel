module
public import RequestProject.TypedTriangle.PaschUnrestrictedInfluence
public import RequestProject.TypedTriangle.PaschFractionalTarget
public import RequestProject.TypedTriangle.TriangleMonitorSeedComparison
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Summing the three unfixed seed factors cancels the cubic unrestricted
Pasch count. No packing hypothesis or completion budget is used. -/
theorem rooted_fractional_influence_le_cube (D : Finset (Finset V))
    (Q : Finset V) (μ : Finset V → ℝ) (C : ℝ)
    (hn : 0 < (Fintype.card V:ℝ)) (hC : 0 ≤ C) (hQ : Q ∈ D) (hQcard : Q.card = 3)
    (hμ0 : ∀ T ∈ D, 0 ≤ μ T)
    (hμ : ∀ T ∈ D, μ T ≤ C/(Fintype.card V:ℝ)) :
    rootedInfluence (fun S => ∏ T ∈ S, μ T) D Q ≤ C^3*μ Q := by
  let n : ℝ := Fintype.card V
  have hMuQ : 0 ≤ μ Q := hμ0 Q hQ
  have hFactor : 0 ≤ (C/n)^3*μ Q := mul_nonneg (pow_nonneg (div_nonneg hC hn.le) _) hMuQ
  have hSum : rootedInfluence (fun S => ∏ T ∈ S, μ T) D Q ≤
      (rootedCount D Q:ℝ)*((C/n)^3*μ Q) := by
    rw [rootedInfluence_eq_sum]
    calc
      _ ≤ ∑ _S ∈ (configurations D).filter (fun S => Q ∈ S), (C/n)^3*μ Q := by
        apply sum_le_sum
        intro S hS
        obtain ⟨hCfg,hQS⟩ := mem_filter.mp hS
        obtain ⟨hSD,hCard,_⟩ := mem_configurations.mp hCfg
        have hProd0 : 0 ≤ ∏ T ∈ S, μ T := prod_nonneg (fun T hT => hμ0 T (hSD hT))
        have hErase : (S.erase Q).card = 3 := by rw [card_erase_of_mem hQS,hCard]
        have hBound : (∏ T ∈ S.erase Q, μ T) ≤ (C/n)^3 := by
          have h := prod_le_prod₀ (s := S.erase Q) (fun T hT => hμ0 T (hSD (mem_of_mem_erase hT)))
            (fun T hT => hμ T (hSD (mem_of_mem_erase hT)))
          simpa only [prod_const,hErase] using h
        rw [abs_of_nonneg hProd0,←prod_erase_mul S μ hQS]
        exact mul_le_mul_of_nonneg_right hBound hMuQ
      _ = (rootedCount D Q:ℝ)*((C/n)^3*μ Q) := by
        rw [sum_const,nsmul_eq_mul]
        rfl
  have hCount : (rootedCount D Q:ℝ) ≤ n^3 := by
    dsimp only [n]
    exact_mod_cast rootedCount_le_cube D Q hQcard
  calc rootedInfluence (fun S => ∏ T ∈ S, μ T) D Q ≤
      (rootedCount D Q:ℝ)*((C/n)^3*μ Q) := hSum
    _ ≤ n^3*((C/n)^3*μ Q) := mul_le_mul_of_nonneg_right hCount hFactor
    _ = C^3*μ Q := by
      have hn' : n ≠ 0 := ne_of_gt hn
      field_simp [hn']

theorem target_loss_of_subset_le (D E : Finset (Finset V)) (μ : Finset V → ℝ) (C : ℝ)
    (hn : 0 < (Fintype.card V:ℝ)) (hC : 0 ≤ C) (hED : E ⊆ D)
    (hCard : ∀ T ∈ D, T.card = 3) (hμ0 : ∀ T ∈ D, 0 ≤ μ T)
    (hμ : ∀ T ∈ D, μ T ≤ C/(Fintype.card V:ℝ)) :
    |target μ D-target μ E| ≤ C^3*(∑ Q ∈ D\E, μ Q) := by
  have hDiff := statistic_difference_le_influences (fun S => ∏ T ∈ S, μ T) D E
  have hEmpty : E\D = ∅ := sdiff_eq_empty_iff_subset.mpr hED
  have hFirst : |target μ D-target μ E| ≤
      ∑ Q ∈ D\E, rootedInfluence (fun S => ∏ T ∈ S, μ T) D Q := by
    simpa only [target,hEmpty,sum_empty,add_zero] using hDiff
  calc |target μ D-target μ E| ≤
      ∑ Q ∈ D\E, rootedInfluence (fun S => ∏ T ∈ S, μ T) D Q := hFirst
    _ ≤ ∑ Q ∈ D\E, C^3*μ Q := by
      apply sum_le_sum
      intro Q hQ
      have hQD := (mem_sdiff.mp hQ).1
      exact rooted_fractional_influence_le_cube D Q μ C hn hC hQD (hCard Q hQD) hμ0 hμ
    _ = C^3*(∑ Q ∈ D\E, μ Q) := by rw [mul_sum]

omit [DecidableEq V] in
theorem reserve_target_loss_le {I : Type*} {H : Host V I} {F : Set (Multiset I)}
    {C : ℝ} {μ : Finset V → ℝ} (hC : 0 < C) (hSeed : IsDiffuseSeed H F C μ)
    (B : Finset (Sym2 V)) (hB : B ⊆ edges H) (hn : 0 < (Fintype.card V:ℝ)) :
    letI : DecidableEq V := Classical.decEq V
    |target μ (allowed H F)-target μ (allowed (residual H B) F)| ≤ C^3*(B.card:ℝ) := by
  letI : DecidableEq V := Classical.decEq V
  have hSub : allowed (residual H B) F ⊆ allowed H F := by
    intro T hT
    exact mem_filter.mpr ⟨mem_univ _,(residual_allowed (isAllowed_of_mem_allowed hT)).1⟩
  have hμ0 : ∀ T ∈ allowed H F, 0 ≤ μ T := by
    intro T hT
    exact (div_nonneg (by norm_num) (mul_nonneg hC.le hn.le)).trans
      (hSeed.1 T (isAllowed_of_mem_allowed hT)).1
  have hLoss := target_loss_of_subset_le (allowed H F) (allowed (residual H B) F) μ C hn hC.le hSub
    (fun T hT => (isAllowed_of_mem_allowed hT).1) hμ0
    (fun T hT => (hSeed.1 T (isAllowed_of_mem_allowed hT)).2)
  have hMass : (∑ Q ∈ allowed H F\allowed (residual H B) F, μ Q) ≤ (B.card:ℝ) :=
    TriangleMonitors.removed_seed_mass_le hC hSeed B hB
  exact hLoss.trans (mul_le_mul_of_nonneg_left hMass (pow_nonneg hC.le 3))

omit [DecidableEq V] in
/-- The reserve loss is O(δ n²), rather than the O(δ n³) bound for
arbitrarily changed integral packing blocks. -/
theorem reserve_target_loss_le_degree {I : Type*} {H : Host V I} {F : Set (Multiset I)}
    {C : ℝ} {μ : Finset V → ℝ} (hC : 0 < C) (hSeed : IsDiffuseSeed H F C μ)
    (B : Finset (Sym2 V)) (hB : B ⊆ edges H) (δ : ℝ)
    (hDegree : ∀ v, (degIn B v:ℝ) ≤ δ*Fintype.card V) (hn : 0 < (Fintype.card V:ℝ)) :
    letI : DecidableEq V := Classical.decEq V
    |target μ (allowed H F)-target μ (allowed (residual H B) F)| ≤
      C^3*(δ*(Fintype.card V:ℝ)^2) := by
  letI : DecidableEq V := Classical.decEq V
  exact (reserve_target_loss_le hC hSeed B hB hn).trans (mul_le_mul_of_nonneg_left
    (TriangleMonitors.edge_card_le_of_degree_bound B δ hDegree) (pow_nonneg hC.le 3))

#print axioms rooted_fractional_influence_le_cube
#print axioms target_loss_of_subset_le
#print axioms reserve_target_loss_le
#print axioms reserve_target_loss_le_degree
end TypedTriangle.Pasch
