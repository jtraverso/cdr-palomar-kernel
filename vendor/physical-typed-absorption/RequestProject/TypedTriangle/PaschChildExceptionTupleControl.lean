module
public import RequestProject.TypedTriangle.PaschAdaptiveAssemblyCore
public import RequestProject.TypedTriangle.PaschMixedBudget
public import RequestProject.TypedTriangle.PaschRawProfileBounds
public import RequestProject.TypedTriangle.PaschSampledTupleControl
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {X V I : Type*} [Fintype X] [Fintype V]

/-- The two actual clone tests needed for two- and three-new-block
interactions. The profile and the packing remain the ones chosen by the
calling packing engine. -/
def childExceptionTupleTests (e : X ↪ V) (A : Finset (Finset X))
    (R : Finset (Finset V)) (μ : Finset X → ℝ) (n : ℝ)
    (ℓ : ℕ) (b : Bool) : Finset (Finset X) → ℝ :=
  if 2 ≤ ℓ ∧ ℓ ≤ 3 then
    embeddedPaddedFloorWeight e A
      (if b then childExceptions R ((univ : Finset X).map e) else ∅) μ n
  else fun _ => 0

theorem childExceptionTupleTests_nonneg (e : X ↪ V) (A : Finset (Finset X))
    (R : Finset (Finset V)) (μ : Finset X → ℝ) (n : ℝ)
    (ℓ : ℕ) (b : Bool) (S : Finset (Finset X)) :
    0 ≤ childExceptionTupleTests e A R μ n ℓ b S := by
  by_cases hRange : 2 ≤ ℓ ∧ ℓ ≤ 3
  · rw [childExceptionTupleTests,if_pos hRange]
    exact embeddedPaddedWeight_nonneg e A _ (floorWeights A μ n)
      (fun T _ => floorWeights_nonneg A μ n T) S
  · simpa only [childExceptionTupleTests,if_neg hRange] using (le_refl (0 : ℝ))

/-- Eligibility is discharged by H3 and the actual coefficient window.
No tuple-eligibility or mass premise survives in the conclusion. -/
theorem child_exception_errors_of_bool_controls {H : Host X I} {F : Set (Multiset I)}
    {μ : Finset X → ℝ} {α C : ℝ} (hH3 : CommonNbrCond H F α)
    (hα : 0 < α) (hC : 1 ≤ C)
    (hLow : ∀ T, IsAllowed H F T → 1/(C*Fintype.card X) ≤ μ T)
    (hUp : ∀ T, IsAllowed H F T → μ T ≤ C/Fintype.card X)
    (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (hN : embeddedMixedEligibilityOrder α C L ≤ Fintype.card X)
    (hL : PairCodegreeBound R L) (hR : ∀ T ∈ R, T.card = 3)
    (P : Finset (Finset X))
    (hControls : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ b : Bool,
      floorTupleTestControl (allowed H F) μ P
        (childExceptionTupleTests e (allowed H F) R μ (Fintype.card X : ℝ) ℓ b) ℓ) :
    ∀ ℓ, 2 ≤ ℓ → ℓ ≤ 3 →
      let A := allowed H F
      let n := (Fintype.card X : ℝ)
      let θ := floorWeights A μ n
      let B := childExceptions R ((univ : Finset X).map e)
      let M := mixedMass (mapConfiguration e A) B (liftTriangleWeight e θ) ℓ
      |PatternStatistics.statistic (completionWeight B) ℓ (mapConfiguration e P)-M| ≤
        (n^2)^(-egj13Epsilon)*(2*(Nat.choose 4 ℓ : ℝ)*target θ A+M) := by
  intro ℓ hℓ2 hℓ3
  let B := childExceptions R ((univ : Finset X).map e)
  have hBL : PairCodegreeBound B L := by
    intro a b hab
    apply (card_le_card ?_).trans (hL a b hab)
    intro T hT
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hT).1).1,(mem_filter.mp hT).2⟩
  have hB : ∀ T ∈ B, T.card = 3 := fun T hT => hR T (mem_filter.mp hT).1
  have hBX : ∀ T ∈ B, 2 ≤ (T ∩ (univ : Finset X).map e).card :=
    fun T hT => (mem_filter.mp hT).2
  exact raw_embedded_mixed_error_of_controls hH3 hα hC hLow hUp e L hN
    B P hBL hB hBX ℓ (by omega) hℓ3
    (by simpa [childExceptionTupleTests,hℓ2,hℓ3,B]
      using hControls ℓ (by omega) (by omega) false)
    (by simpa [childExceptionTupleTests,hℓ2,hℓ3,B]
      using hControls ℓ (by omega) (by omega) true)

/-- Capped raw loads suffice for the floor target upper bound; exact
physicality and an exact diffuse seed are unnecessary. -/
theorem floor_target_le_of_capped_profile {H : Host X I} {F : Set (Multiset I)}
    {μ : Finset X → ℝ} {C : ℝ} (hC : 0 < C) (hn : 0 < Fintype.card X)
    (hLow : ∀ T, IsAllowed H F T → 1/(C*Fintype.card X) ≤ μ T)
    (hUp : ∀ T, IsAllowed H F T → μ T ≤ C/Fintype.card X)
    (hLoad : ∀ f ∈ edges H, bdry H F μ f ≤ 1) :
    target (floorWeights (allowed H F) μ (Fintype.card X : ℝ)) (allowed H F) ≤
      C^3*(Fintype.card X : ℝ)^2/4 := by
  let A := allowed H F
  let n := (Fintype.card X : ℝ)
  let θ := floorWeights A μ n
  have hn0 : 0 < n := by dsimp only [n]; exact_mod_cast hn
  have hμ0 : ∀ T ∈ A, 0 ≤ μ T := fun T hT =>
    (by positivity : (0 : ℝ) ≤ 1/(C*n)).trans (hLow T (isAllowed_of_mem_allowed hT))
  have hFloor : ∀ T ∈ A, θ T ≤ μ T := fun T hT =>
    (floorWeights_bounds A μ hC hn0
      (fun Q hQ => hLow Q (isAllowed_of_mem_allowed hQ)) hT).2
  have hMass : (∑ T ∈ A, θ T) ≤ n^2 :=
    (sum_le_sum hFloor).trans (raw_profile_mass_cap hμ0 hLoad)
  have hTarget := target_le_cube_times_seed_mass A θ hC.le hn
    (fun T hT => (isAllowed_of_mem_allowed hT).1)
    (fun T _ => floorWeights_nonneg A μ n T)
    (fun T hT => (hFloor T hT).trans (hUp T (isAllowed_of_mem_allowed hT)))
  have hPay := mul_le_mul_of_nonneg_left hMass (pow_nonneg hC.le 3)
  linarith only [hTarget,hPay]

private theorem child_exception_upper_from_target {H : Host X I} {F : Set (Multiset I)}
    {μ : Finset X → ℝ} {α C : ℝ} (hH3 : CommonNbrCond H F α)
    (hα : 0 < α) (hC : 1 ≤ C)
    (hLow : ∀ T, IsAllowed H F T → 1/(C*Fintype.card X) ≤ μ T)
    (hUp : ∀ T, IsAllowed H F T → μ T ≤ C/Fintype.card X)
    (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (hN : embeddedMixedEligibilityOrder α C L ≤ Fintype.card X)
    (hL : PairCodegreeBound R L) (hR : ∀ T ∈ R, T.card = 3)
    (P : Finset (Finset X))
    (hControls : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ b : Bool,
      floorTupleTestControl (allowed H F) μ P
        (childExceptionTupleTests e (allowed H F) R μ (Fintype.card X : ℝ) ℓ b) ℓ)
    (hTarget : target (floorWeights (allowed H F) μ (Fintype.card X : ℝ)) (allowed H F) ≤
      C^3*(Fintype.card X : ℝ)^2/4) :
    ∀ D : Finset (Finset X), D ⊆ P →
      PatternStatistics.statistic
        (completionWeight (childExceptions R ((univ : Finset X).map e))) 2 (mapConfiguration e D)+
      PatternStatistics.statistic
        (completionWeight (childExceptions R ((univ : Finset X).map e))) 3 (mapConfiguration e D) ≤
      (2*(6*(L : ℝ)*C^2+C^3)*(L : ℝ)+5*C^3)*(Fintype.card X : ℝ)^2 := by
  let A := allowed H F
  let n := (Fintype.card X : ℝ)
  let θ := floorWeights A μ n
  let U := (univ : Finset X).map e
  let ρ := (n^2)^(-egj13Epsilon)
  have hSix : 6 ≤ Fintype.card X :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hN))
  have hn : 0 < Fintype.card X := by omega
  have hn0 : 0 < n := by dsimp only [n]; exact_mod_cast hn
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hUCard : U.card = Fintype.card X := by simp only [U,card_map,card_univ]
  have hFloor : ∀ T ∈ A, θ T ≤ C/n := by
    intro T hT
    exact (floorWeights_bounds A μ hC0 hn0
      (fun Q hQ => hLow Q (isAllowed_of_mem_allowed hQ)) hT).2.trans
        (hUp T (isAllowed_of_mem_allowed hT))
  have hInside : ∀ T ∈ mapConfiguration e A, T ⊆ U := by
    intro T hT
    obtain ⟨Q,hQ,rfl⟩ := mem_mapConfiguration.mp hT
    exact map_subset_map.mpr (subset_univ Q)
  have hθ0 : ∀ T ∈ mapConfiguration e A, 0 ≤ liftTriangleWeight e θ T := by
    intro T hT
    obtain ⟨Q,hQ,rfl⟩ := mem_mapConfiguration.mp hT
    rw [liftTriangleWeight_map]
    exact floorWeights_nonneg A μ n Q
  have hθb : ∀ T ∈ mapConfiguration e A,
      liftTriangleWeight e θ T ≤ C/(U.card : ℝ) := by
    intro T hT
    obtain ⟨Q,hQ,rfl⟩ := mem_mapConfiguration.mp hT
    rw [liftTriangleWeight_map,hUCard]
    exact hFloor Q hQ
  have hTargetMap : target (liftTriangleWeight e θ) (mapConfiguration e A) ≤
      C^3*(U.card : ℝ)^2/4 := by
    rw [pasch_target_mapConfiguration,hUCard]
    simpa only [liftTriangleWeight_map] using hTarget
  have hErrors := child_exception_errors_of_bool_controls hH3 hα hC hLow hUp e R L hN hL hR P hControls
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (sq_nonneg n) _
  have hn1R : (1 : ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast (show 1 ≤ Fintype.card X by omega)
  have hρ1 : ρ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (one_le_pow₀ hn1R) (by norm_num [egj13Epsilon])
  have hTargetEq : target (liftTriangleWeight e θ) (mapConfiguration e A) = target θ A := by
    rw [pasch_target_mapConfiguration]
    simp only [liftTriangleWeight_map]
  have hErrorsMap (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ) (hℓ3 : ℓ ≤ 3) :
      |PatternStatistics.statistic (completionWeight (childExceptions R U)) ℓ (mapConfiguration e P)-
        mixedMass (mapConfiguration e A) (childExceptions R U) (liftTriangleWeight e θ) ℓ| ≤
      ρ*(2*(Nat.choose 4 ℓ : ℝ)*target (liftTriangleWeight e θ) (mapConfiguration e A)+
        mixedMass (mapConfiguration e A) (childExceptions R U) (liftTriangleWeight e θ) ℓ) := by
    rw [hTargetEq]
    exact hErrors ℓ hℓ2 hℓ3
  have hUpper := child_exception_mixed_statistics_le
    (mapConfiguration e A) (mapConfiguration e P) R U (liftTriangleWeight e θ) C ρ L
    hC0.le hρ0 hρ1 (by rw [hUCard]; exact hn) hL hR hInside hθ0 hθb hTargetMap hErrorsMap
  rw [hUCard] at hUpper
  intro D hDP
  have hMapDP := (mapConfiguration_subset_iff e D P).mpr hDP
  have hMono2 := PatternStatistics.statistic_mono_of_nonnegative
    (completionWeight (childExceptions R U)) 2 (mapConfiguration e D) (mapConfiguration e P)
    hMapDP (completionWeight_nonneg _)
  have hMono3 := PatternStatistics.statistic_mono_of_nonnegative
    (completionWeight (childExceptions R U)) 3 (mapConfiguration e D) (mapConfiguration e P)
    hMapDP (completionWeight_nonneg _)
  exact (add_le_add hMono2 hMono3).trans hUpper

/-- The actual raw near-packing and every sampled subfamily inherit the
quadratic exception bound. The only load premise is the proved cap at one. -/
theorem child_exception_statistics_le_of_capped_bool_controls
    {H : Host X I} {F : Set (Multiset I)} {μ : Finset X → ℝ} {α C : ℝ}
    (hH3 : CommonNbrCond H F α) (hα : 0 < α) (hC : 1 ≤ C)
    (hLow : ∀ T, IsAllowed H F T → 1/(C*Fintype.card X) ≤ μ T)
    (hUp : ∀ T, IsAllowed H F T → μ T ≤ C/Fintype.card X)
    (hLoad : ∀ f ∈ edges H, bdry H F μ f ≤ 1)
    (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (hN : embeddedMixedEligibilityOrder α C L ≤ Fintype.card X)
    (hL : PairCodegreeBound R L) (hR : ∀ T ∈ R, T.card = 3)
    (P : Finset (Finset X))
    (hControls : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ b : Bool,
      floorTupleTestControl (allowed H F) μ P
        (childExceptionTupleTests e (allowed H F) R μ (Fintype.card X : ℝ) ℓ b) ℓ) :
    ∀ D : Finset (Finset X), D ⊆ P →
      PatternStatistics.statistic
        (completionWeight (childExceptions R ((univ : Finset X).map e))) 2 (mapConfiguration e D)+
      PatternStatistics.statistic
        (completionWeight (childExceptions R ((univ : Finset X).map e))) 3 (mapConfiguration e D) ≤
      (2*(6*(L : ℝ)*C^2+C^3)*(L : ℝ)+5*C^3)*(Fintype.card X : ℝ)^2 := by
  have hSix : 6 ≤ Fintype.card X :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hN))
  exact child_exception_upper_from_target hH3 hα hC hLow hUp e R L hN hL hR P hControls
    (floor_target_le_of_capped_profile (lt_of_lt_of_le zero_lt_one hC)
      (by omega) hLow hUp hLoad)

/-- Exact seeds use their already proved floor target cap, on the same
literal profile and packing selected by the protected packing producer. -/
theorem child_exception_statistics_le_of_seed_bool_controls
    {H : Host X I} {F : Set (Multiset I)} {μ : Finset X → ℝ} {α C : ℝ}
    (hSeed : IsDiffuseSeed H F C μ) (hH3 : CommonNbrCond H F α)
    (hα : 0 < α) (hC : 1 ≤ C)
    (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (hN : embeddedMixedEligibilityOrder α C L ≤ Fintype.card X)
    (hL : PairCodegreeBound R L) (hR : ∀ T ∈ R, T.card = 3)
    (P : Finset (Finset X))
    (hControls : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ b : Bool,
      floorTupleTestControl (allowed H F) μ P
        (childExceptionTupleTests e (allowed H F) R μ (Fintype.card X : ℝ) ℓ b) ℓ) :
    ∀ D : Finset (Finset X), D ⊆ P →
      PatternStatistics.statistic
        (completionWeight (childExceptions R ((univ : Finset X).map e))) 2 (mapConfiguration e D)+
      PatternStatistics.statistic
        (completionWeight (childExceptions R ((univ : Finset X).map e))) 3 (mapConfiguration e D) ≤
      (2*(6*(L : ℝ)*C^2+C^3)*(L : ℝ)+5*C^3)*(Fintype.card X : ℝ)^2 := by
  have hSix : 6 ≤ Fintype.card X :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hN))
  exact child_exception_upper_from_target hH3 hα hC
    (fun T hT => (hSeed.1 T hT).1) (fun T hT => (hSeed.1 T hT).2)
    e R L hN hL hR P hControls
    (floor_target_le_seed_order_square hSeed (lt_of_lt_of_le zero_lt_one hC) (by omega))

#print axioms childExceptionTupleTests_nonneg
#print axioms child_exception_errors_of_bool_controls
#print axioms floor_target_le_of_capped_profile
#print axioms child_exception_statistics_le_of_capped_bool_controls
#print axioms child_exception_statistics_le_of_seed_bool_controls
end TypedTriangle.Pasch
