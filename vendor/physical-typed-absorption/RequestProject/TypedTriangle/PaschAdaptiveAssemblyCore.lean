module
public import RequestProject.TypedTriangle.PaschAmbientCellModes
public import RequestProject.TypedTriangle.PaschAmbientRootedMonitor
public import RequestProject.TypedTriangle.PaschDepthBudget
public import RequestProject.TypedTriangle.PaschEmbeddingStatistics
public import RequestProject.TypedTriangle.PaschExceptionReduction
public import RequestProject.TypedTriangle.PaschFloorInputs
public import RequestProject.TypedTriangle.PaschFloorMixedControl
public import RequestProject.TypedTriangle.PaschPaddedMixedAssembly
public import RequestProject.TypedTriangle.PaschRawEmbeddedEligibility
public import RequestProject.TypedTriangle.PaschSmallRemainder
public import RequestProject.TypedTriangle.VortexPrescribedRawPathsAmbientAssembly
public import RequestProject.TypedTriangle.VortexRawPathsPaidAssemblyBase
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

-- Source segment: PaschEmbeddedMixedControl.lean
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {X V I : Type*} [Fintype X] [Fintype V]

theorem embedded_statistic_padded_sub_baseline (e : X ↪ V) (A P : Finset (Finset X))
    (B : Finset (Finset V)) (θ : Finset X → ℝ) (ℓ : ℕ) (hℓ : ℓ ≤ 3) :
    PatternStatistics.statistic (embeddedPaddedWeight e A B θ) ℓ P -
      PatternStatistics.statistic (embeddedPaddedWeight e A ∅ θ) ℓ P =
        PatternStatistics.statistic (completionWeight B) ℓ (mapConfiguration e P) := by
  rw [tuple_statistic_mapConfiguration]
  unfold PatternStatistics.statistic
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro S hS
  have hc := (mem_powersetCard.mp hS).2
  have hMapCard : (mapConfiguration e S).card < 4 := by
    simpa only [mapConfiguration,card_map] using (show S.card < 4 by omega)
  have hz := completionWeight_empty_of_card_lt_four (mapConfiguration e S) hMapCard
  simp only [embeddedPaddedWeight,embeddedCompletionWeight,hz]
  ring

theorem raw_embedded_floor_control_estimate {H : Host X I} {F : Set (Multiset I)}
    {μ : Finset X → ℝ} {α C : ℝ} (hH3 : CommonNbrCond H F α)
    (hα : 0 < α) (hC : 1 ≤ C)
    (hLow : ∀ T, IsAllowed H F T → 1/(C*Fintype.card X) ≤ μ T)
    (hUp : ∀ T, IsAllowed H F T → μ T ≤ C/Fintype.card X)
    (e : X ↪ V) (L : ℕ) (hN : embeddedMixedEligibilityOrder α C L ≤ Fintype.card X)
    (B : Finset (Finset V)) (P : Finset (Finset X)) (hL : PairCodegreeBound B L)
    (hB : ∀ T ∈ B, T.card = 3)
    (hBX : ∀ T ∈ B, 2 ≤ (T ∩ (univ : Finset X).map e).card)
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ3 : ℓ ≤ 3)
    (hControl : floorTupleTestControl (allowed H F) μ P
      (embeddedPaddedFloorWeight e (allowed H F) B μ (Fintype.card X : ℝ)) ℓ) :
    let A := allowed H F
    let n := (Fintype.card X : ℝ)
    let θ := floorWeights A μ n
    let M := mixedMass (mapConfiguration e A) B (liftTriangleWeight e θ) ℓ
    |PatternStatistics.statistic (embeddedPaddedWeight e A B θ) ℓ P -
      ((Nat.choose 4 ℓ : ℝ)*target θ A+M)| ≤
      (n^2)^(-egj13Epsilon)*((Nat.choose 4 ℓ : ℝ)*target θ A+M) := by
  have hEligible : ∀ j, 1 ≤ j → j ≤ ℓ → ∀ R : Finset (allowed H F), R.card = j →
      WeightedClone.tupleExtensionMass (indexedPackets (allowed H F))
        (floorCopies (allowed H F) μ (Fintype.card X : ℝ))
        (indexedTupleWeight (allowed H F)
          (embeddedPaddedFloorWeight e (allowed H F) B μ (Fintype.card X : ℝ))) ℓ R *
          ((Fintype.card X : ℝ)^2)^((j : ℝ)+1/4) ≤
      WeightedClone.tupleMass (indexedPackets (allowed H F))
        (floorCopies (allowed H F) μ (Fintype.card X : ℝ))
        (indexedTupleWeight (allowed H F)
          (embeddedPaddedFloorWeight e (allowed H F) B μ (Fintype.card X : ℝ))) ℓ := by
    intro j hj hjℓ R hR
    have hh := raw_embedded_padded_tuple_eligible hH3 hα hC hLow hUp e L hN B hL hB hBX
      ℓ hℓ1 hℓ3 R (by omega) (by omega)
    simpa only [hR] using hh
  have hh := hControl hEligible
  rw [embedded_padded_floor_actual_mass_div] at hh
  exact hh

theorem raw_embedded_mixed_error_of_controls {H : Host X I} {F : Set (Multiset I)}
    {μ : Finset X → ℝ} {α C : ℝ} (hH3 : CommonNbrCond H F α)
    (hα : 0 < α) (hC : 1 ≤ C)
    (hLow : ∀ T, IsAllowed H F T → 1/(C*Fintype.card X) ≤ μ T)
    (hUp : ∀ T, IsAllowed H F T → μ T ≤ C/Fintype.card X)
    (e : X ↪ V) (L : ℕ) (hN : embeddedMixedEligibilityOrder α C L ≤ Fintype.card X)
    (B : Finset (Finset V)) (P : Finset (Finset X)) (hL : PairCodegreeBound B L)
    (hB : ∀ T ∈ B, T.card = 3)
    (hBX : ∀ T ∈ B, 2 ≤ (T ∩ (univ : Finset X).map e).card)
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ3 : ℓ ≤ 3)
    (hBase : floorTupleTestControl (allowed H F) μ P
      (embeddedPaddedFloorWeight e (allowed H F) ∅ μ (Fintype.card X : ℝ)) ℓ)
    (hBank : floorTupleTestControl (allowed H F) μ P
      (embeddedPaddedFloorWeight e (allowed H F) B μ (Fintype.card X : ℝ)) ℓ) :
    let A := allowed H F
    let n := (Fintype.card X : ℝ)
    let θ := floorWeights A μ n
    let M := mixedMass (mapConfiguration e A) B (liftTriangleWeight e θ) ℓ
    |PatternStatistics.statistic (completionWeight B) ℓ (mapConfiguration e P)-M| ≤
      (n^2)^(-egj13Epsilon)*(2*(Nat.choose 4 ℓ : ℝ)*target θ A+M) := by
  have hEmptyL : PairCodegreeBound (∅ : Finset (Finset V)) L := by
    intro a b hab
    simp
  have hEmptyB : ∀ T ∈ (∅ : Finset (Finset V)), T.card = 3 := by simp
  have hEmptyX : ∀ T ∈ (∅ : Finset (Finset V)),
      2 ≤ (T ∩ (univ : Finset X).map e).card := by simp
  have hBase' := raw_embedded_floor_control_estimate hH3 hα hC hLow hUp e L hN
    ∅ P hEmptyL hEmptyB hEmptyX ℓ hℓ1 hℓ3 hBase
  dsimp only at hBase'
  rw [mixedMass_empty_of_arity_le_three _ _ ℓ hℓ3,add_zero] at hBase'
  have hBank' := raw_embedded_floor_control_estimate hH3 hα hC hLow hUp e L hN
    B P hL hB hBX ℓ hℓ1 hℓ3 hBank
  let A := allowed H F
  let n := (Fintype.card X : ℝ)
  let θ := floorWeights A μ n
  let M := mixedMass (mapConfiguration e A) B (liftTriangleWeight e θ) ℓ
  let b := (Nat.choose 4 ℓ : ℝ)*target θ A
  let s := PatternStatistics.statistic (embeddedPaddedWeight e A B θ) ℓ P
  let t := PatternStatistics.statistic (embeddedPaddedWeight e A ∅ θ) ℓ P
  let z := PatternStatistics.statistic (completionWeight B) ℓ (mapConfiguration e P)
  let ρ := (n^2)^(-egj13Epsilon)
  change |t-b| ≤ ρ*b at hBase'
  change |s-(b+M)| ≤ ρ*(b+M) at hBank'
  suffices hFinal : |z-M| ≤ ρ*(2*b+M) by
    convert hFinal using 1 <;> dsimp only [b] <;> ring
  have hId : s-t = z := embedded_statistic_padded_sub_baseline e A P B θ ℓ hℓ3
  have hTri := abs_add_le (s-(b+M)) (-(t-b))
  simp only [abs_neg] at hTri
  rw [←sub_eq_add_neg] at hTri
  have hEq : (s-(b+M))-(t-b) = z-M := by rw [←hId]; ring
  rw [hEq] at hTri
  nlinarith only [hTri,hBase',hBank']

#print axioms embedded_statistic_padded_sub_baseline
#print axioms raw_embedded_floor_control_estimate
#print axioms raw_embedded_mixed_error_of_controls
end TypedTriangle.Pasch

namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V]

/-- The two- and three-new-block tests have quadratic child cost even for
an entire ambient mode universe. This is also valid for the raw packing
which witnesses a subsequently sampled stock family. -/
theorem child_exception_mixed_statistics_le (A P R : Finset (Finset V))
    (X : Finset V) (θ : Finset V → ℝ) (C ρ : ℝ) (L : ℕ)
    (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hX : 0 < X.card)
    (hL : PairCodegreeBound R L) (hR : ∀ T ∈ R, T.card = 3)
    (hAX : ∀ T ∈ A, T ⊆ X) (hθ0 : ∀ T ∈ A, 0 ≤ θ T)
    (hθb : ∀ T ∈ A, θ T ≤ C/(X.card : ℝ))
    (hTarget : target θ A ≤ C^3*(X.card : ℝ)^2/4)
    (hErrors : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ 3 →
      |PatternStatistics.statistic (completionWeight (childExceptions R X)) ℓ P-
        mixedMass A (childExceptions R X) θ ℓ| ≤
        ρ*(2*(Nat.choose 4 ℓ : ℝ)*target θ A+mixedMass A (childExceptions R X) θ ℓ)) :
    PatternStatistics.statistic (completionWeight (childExceptions R X)) 2 P+
      PatternStatistics.statistic (completionWeight (childExceptions R X)) 3 P ≤
      (2*(6*(L : ℝ)*C^2+C^3)*(L : ℝ)+5*C^3)*(X.card : ℝ)^2 := by
  let B := childExceptions R X
  have hBL : PairCodegreeBound B L := by
    intro a b hab
    apply (card_le_card ?_).trans (hL a b hab)
    intro T hT
    obtain ⟨hTB,hPair⟩ := mem_filter.mp hT
    exact mem_filter.mpr ⟨(mem_filter.mp hTB).1,hPair⟩
  have hB : ∀ T ∈ B, T.card = 3 := fun T hT => hR T (mem_filter.mp hT).1
  have hBX : ∀ T ∈ B, 2 ≤ (T ∩ X).card := fun T hT => (mem_filter.mp hT).2
  have hBC : B.card ≤ X.card^2*L :=
    (exception_family_card_le B X L hBL hBX).trans
      (Nat.mul_le_mul_right L (Nat.choose_le_pow X.card 2))
  have hBCR : (B.card : ℝ) ≤ (X.card : ℝ)^2*(L : ℝ) := by exact_mod_cast hBC
  have hM2 := mixedMass_two_le_on_child A B X θ C L hC hX hBL hAX hB hBX hθ0 hθb
  have hM3 := mixedMass_three_le_on_child A B X θ C hC hX hAX hB hθ0 hθb
  have hCardPay := mul_le_mul_of_nonneg_left hBCR
    (show (0 : ℝ) ≤ 6*(L : ℝ)*C^2+C^3 by positivity)
  have hMass : mixedMass A B θ 2+mixedMass A B θ 3 ≤
      (6*(L : ℝ)*C^2+C^3)*(L : ℝ)*(X.card : ℝ)^2 := by
    nlinarith only [hM2,hM3,hCardPay]
  have hT0 := target_nonneg_on A θ hθ0
  have hM20 := mixedMass_nonneg A B θ 2 hθ0
  have hM30 := mixedMass_nonneg A B θ 3 hθ0
  have h2 := (abs_le.mp (hErrors 2 (by omega) (by omega))).2
  have h3 := (abs_le.mp (hErrors 3 (by omega) (by omega))).2
  norm_num only [Nat.choose, Nat.cast_ofNat] at h2 h3
  have hRhoPay := mul_le_mul_of_nonneg_right hρ1
    (show 0 ≤ 20*target θ A+mixedMass A B θ 2+mixedMass A B θ 3 by positivity)
  dsimp only [B] at hMass hRhoPay
  nlinarith only [h2,h3,hMass,hRhoPay,hTarget]

#print axioms child_exception_mixed_statistics_le
end TypedTriangle.Pasch

-- Source segment: PaschAmbientMixedIncrement.lean
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace TypedTriangle.Pasch
variable {X V : Type*} [Fintype X] [Fintype V]

theorem completionCount_singleton_le_rooted (R : Finset (Finset V)) (T : Finset V) :
    completionCount R {T} ≤ rootedCount (insert T R) T := by
  apply card_le_card
  intro K hK
  obtain ⟨hConf,hDiff⟩ := mem_filter.mp hK
  have hTK : T ∈ K := (mem_sdiff.mp (hDiff.symm ▸ mem_singleton_self T)).1
  have hSub : K ⊆ insert T R := by
    simpa only [singleton_union] using (mem_configurations.mp hConf).1
  exact mem_filter.mpr ⟨mem_configurations.mpr
    ⟨hSub,(mem_configurations.mp hConf).2⟩,hTK⟩

theorem one_new_cross_le_ambient_monitor (e : X ↪ V) (P : Finset (Finset X))
    (R : Finset (Finset V)) (L : ℕ) (K : ℝ)
    (hn : 0 < Fintype.card V) (hMonitor : (∑ T ∈ P, childPaddedWeight e R L T) ≤ K) :
    PatternStatistics.statistic (completionWeight R) 1 (mapConfiguration e P) ≤
      2*(Fintype.card V : ℝ)*((L+1 : ℕ) : ℝ)^3*K := by
  let den := (Fintype.card V : ℝ)*((L+1 : ℕ) : ℝ)^3
  have hn0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : 0 < den := by dsimp only [den]; positivity
  have hPoint (T : Finset X) : completionWeight R {T.map e} ≤
      2*den*childPaddedWeight e R L T := by
    have hCount : (completionCount R {T.map e} : ℝ) ≤ rootedCount (insert (T.map e) R) (T.map e) := by
      exact_mod_cast completionCount_singleton_le_rooted R (T.map e)
    have hEq : (rootedCount (insert (T.map e) R) (T.map e) : ℝ) =
        den*ambientRootedWeight R L (T.map e) := by
      unfold ambientRootedWeight
      change _ = den*(_/den)
      field_simp [ne_of_gt hd]
    have hPad : ambientRootedWeight R L (T.map e) ≤ 2*childPaddedWeight e R L T := by
      unfold childPaddedWeight
      have hh : (0 : ℝ) ≤ 1/(Fintype.card X : ℝ) := by positivity
      linarith only [hh]
    change (completionCount R {T.map e} : ℝ) ≤ _
    exact hCount.trans (hEq.le.trans ((mul_le_mul_of_nonneg_left hPad hd.le).trans_eq (by ring)))
  have hStat : PatternStatistics.statistic (completionWeight R) 1 (mapConfiguration e P) =
      ∑ T ∈ P, completionWeight R {T.map e} := by
    rw [tuple_statistic_mapConfiguration]
    unfold PatternStatistics.statistic
    rw [powersetCard_one,sum_map]
    rfl
  rw [hStat]
  calc
    _ ≤ ∑ T ∈ P, 2*den*childPaddedWeight e R L T := sum_le_sum (fun T _ => hPoint T)
    _ = 2*den*(∑ T ∈ P, childPaddedWeight e R L T) := (mul_sum _ _ _).symm
    _ ≤ 2*den*K := mul_le_mul_of_nonneg_left hMonitor (by positivity)
    _ = _ := by ring

/-- One new block uses the ambient monitor. Two and three new blocks use
the exact child exception tests. This retains all ambient interactions. -/
theorem embedded_packing_union_count_increment (e : X ↪ V) (P : Finset (Finset X))
    (R : Finset (Finset V)) (L : ℕ) (K : ℝ) (hn : 0 < Fintype.card V)
    (hMonitor : (∑ T ∈ P, childPaddedWeight e R L T) ≤ K) :
    (count (mapConfiguration e P ∪ R) : ℝ) ≤ count R+count P+
      2*(Fintype.card V : ℝ)*((L+1 : ℕ) : ℝ)^3*K+
      PatternStatistics.statistic (completionWeight (childExceptions R ((univ : Finset X).map e)))
        2 (mapConfiguration e P)+
      PatternStatistics.statistic (completionWeight (childExceptions R ((univ : Finset X).map e)))
        3 (mapConfiguration e P) := by
  have hInside : ∀ T ∈ mapConfiguration e P, T ⊆ (univ : Finset X).map e := by
    intro T hT
    obtain ⟨Q,hQ,rfl⟩ := mem_mapConfiguration.mp hT
    exact map_subset_map.mpr (subset_univ Q)
  have hUnion := count_union_le_mixed_statistics R (mapConfiguration e P)
  rw [count_mapConfiguration,
    completion_statistic_childExceptions R (mapConfiguration e P) ((univ : Finset X).map e) 2 (by omega) hInside,
    completion_statistic_childExceptions R (mapConfiguration e P) ((univ : Finset X).map e) 3 (by omega) hInside] at hUnion
  have hOne := one_new_cross_le_ambient_monitor e P R L K hn hMonitor
  linarith only [hUnion,hOne]

#print axioms completionCount_singleton_le_rooted
#print axioms one_new_cross_le_ambient_monitor
#print axioms embedded_packing_union_count_increment
end TypedTriangle.Pasch

-- Source segment: PaschTrackedCompletion.lean
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

/-- Assemble the count certificate of the controlled prefix with an exact
completion of its small remainder. All families and containments are literal,
and the target remains the one chosen for the original host. -/
theorem tracked_completion_target_error {H : Host V I} {F : Set (Multiset I)}
    (base paid D : Finset (Finset V)) (U : ℕ → Finset (Finset V))
    (a : ℕ → ℝ) (N K m : ℕ) (cost q β σ τ targetValue : ℝ)
    (hCost : 0 ≤ cost) (hq : 0 ≤ q) (hβ : 0 ≤ β) (hτ : 0 < τ)
    (hn : 0 < Fintype.card V) (ha : ∀ j, 0 ≤ a j)
    (hShrink : ∀ j, a (j+1) ≤ a j/16)
    (hFirst : a 0 ≤ 2*q*Fintype.card V)
    (hInit : (count (U 0) : ℝ) ≤ count base+β*(Fintype.card V : ℝ)^2)
    (hStep : ∀ j, (count (U (j+1)) : ℝ) ≤ count (U j)+
      cost*Fintype.card V*((j : ℝ)+1)^3*a j)
    (hBasePaid : base ⊆ paid) (hPaidUniverse : paid ⊆ U N)
    (hPaid : IsPacking H F paid) (hD : IsDecomposition H F (edges H) D)
    (hPaidD : paid ⊆ D)
    (hCut : m ≤ Nat.sqrt (Nat.sqrt (Fintype.card V)))
    (hReserve : ⌈(K : ℝ)/τ⌉₊ ≤ Fintype.card V)
    (hSqrt : ⌈1/τ^2⌉₊ ≤ Fintype.card V)
    (hRest : (edges H \ paid.biUnion triEdges).card ≤ K+m^2)
    (hTarget : |(count base : ℝ)-targetValue| ≤ σ*(Fintype.card V : ℝ)^2) :
    |(count D : ℝ)-targetValue| ≤
      (σ+β+4*cost*q+2*τ)*(Fintype.card V : ℝ)^2 := by
  let n := (Fintype.card V : ℝ)
  have hn0 : 0 ≤ n := by dsimp only [n]; positivity
  have hSum := adaptive_cubic_cost_sum_bound a cost n q hCost hn0 ha hShrink hFirst N
  have hPrefix := count_prefix_budget U (fun j => cost*n*((j : ℝ)+1)^3*a j) hStep N
  have hCount : (count (U N) : ℝ) ≤ count base+(β+4*cost*q)*n^2 := by
    nlinarith only [hInit,hSum,hPrefix]
  have hSpent0 : 0 ≤ (β+4*cost*q)*n^2 := by positivity
  have hPaidTarget := adaptive_sandwich_target_error base (U N) paid targetValue σ
    (β+4*cost*q) ((β+4*cost*q)*n^2) hBasePaid hPaidUniverse hCount hSpent0 le_rfl hTarget
  have hFinal := small_remainder_completion_target_error hPaid hD hPaidD K m τ
    (σ+(β+4*cost*q)) targetValue hτ hn hCut hReserve hSqrt hRest hPaidTarget
  convert hFinal using 1 <;> ring

#print axioms tracked_completion_target_error
end TypedTriangle.Pasch

-- Source segment: PaschPaidPrefix.lean
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open AmbientBank

/-- A paid prefix keeps its actual decomposition and the exact remaining
child graph. The reserved absorber remains a separate literal edge family. -/
structure PaidPrefix {V X I : Type*} [Fintype V] [Fintype X]
    (H : Host V I) (F : Set (Multiset I)) (reserved : Finset (Sym2 V))
    (J : Host X I) (e : X ↪ V) where
  paidEdges : Finset (Sym2 V)
  paid : Finset (Finset V)
  decomposition : IsDecomposition H F paidEdges paid
  partition : edges H = paidEdges ∪ (reserved ∪ liftEdges e (edges J))
  paid_disjoint : Disjoint paidEdges (reserved ∪ liftEdges e (edges J))
  reserve_child : Disjoint reserved (liftEdges e (edges J))

namespace PaidPrefix
variable {V X Y I : Type*} [Fintype V] [Fintype X] [Fintype Y]

theorem liftEdges_union (e : X ↪ V) (A B : Finset (Sym2 X)) :
    liftEdges e (A ∪ B) = liftEdges e A ∪ liftEdges e B := by
  unfold liftEdges
  exact map_union _ _

theorem liftEdges_comp (f : Y ↪ X) (e : X ↪ V) (A : Finset (Sym2 Y)) :
    liftEdges (f.trans e) A = liftEdges e (liftEdges f A) := by
  unfold liftEdges
  rw [map_map]
  congr 1
  ext z
  induction z using Sym2.ind with
  | h a b => rfl

theorem liftEdges_mono (e : X ↪ V) {A B : Finset (Sym2 X)} (hAB : A ⊆ B) :
    liftEdges e A ⊆ liftEdges e B := map_subset_map.mpr hAB

theorem liftEdges_disjoint (e : X ↪ V) {A B : Finset (Sym2 X)} (hAB : Disjoint A B) :
    Disjoint (liftEdges e A) (liftEdges e B) := (disjoint_map _).mpr hAB

/-- Append a concrete paid layer without reselecting any of its blocks. -/
def append {H : Host V I} {F : Set (Multiset I)} {reserved : Finset (Sym2 V)}
    {J : Host X I} {e : X ↪ V} (p : PaidPrefix H F reserved J e)
    (Jnext : Host Y I) (f : Y ↪ X)
    (hAdj : ∀ x y, J.G.Adj x y → H.G.Adj (e x) (e y))
    (hLab : ∀ x, J.lab x = H.lab (e x))
    (E : Finset (Sym2 X)) (D : Finset (Finset X))
    (hD : IsDecomposition J F E D)
    (hPartition : edges J = E ∪ liftEdges f (edges Jnext))
    (hDisjoint : Disjoint E (liftEdges f (edges Jnext))) :
    PaidPrefix H F reserved Jnext (f.trans e) := by
  have hE : E ⊆ edges J := by rw [hPartition]; exact subset_union_left
  have hNext : liftEdges f (edges Jnext) ⊆ edges J := by
    rw [hPartition]
    exact subset_union_right
  have hE' := liftEdges_mono e hE
  have hNext' : liftEdges (f.trans e) (edges Jnext) ⊆ liftEdges e (edges J) := by
    rw [liftEdges_comp]
    exact liftEdges_mono e hNext
  have hPaidE : Disjoint p.paidEdges (liftEdges e E) :=
    (p.paid_disjoint.mono_right subset_union_right).mono_right hE'
  have hLiftD := decomposition_lift J H F e hAdj hLab hD
  have hBoth := p.decomposition.union hLiftD hPaidE
  refine ⟨p.paidEdges ∪ liftEdges e E,p.paid ∪ mapConfiguration e D,hBoth,?_,?_,
    p.reserve_child.mono_right hNext'⟩
  · rw [p.partition,hPartition,liftEdges_union,←liftEdges_comp]
    ac_rfl
  · apply disjoint_union_left.mpr
    constructor
    · exact disjoint_union_right.mpr
        ⟨p.paid_disjoint.mono_right subset_union_left,
          (p.paid_disjoint.mono_right subset_union_right).mono_right hNext'⟩
    · apply disjoint_union_right.mpr
      constructor
      · exact (p.reserve_child.mono_right hE').symm
      · rw [liftEdges_comp]
        exact liftEdges_disjoint e hDisjoint

theorem paid_subset_append {H : Host V I} {F : Set (Multiset I)}
    {reserved : Finset (Sym2 V)} {J : Host X I} {e : X ↪ V}
    (p : PaidPrefix H F reserved J e) (Jnext : Host Y I) (f : Y ↪ X)
    (hAdj : ∀ x y, J.G.Adj x y → H.G.Adj (e x) (e y))
    (hLab : ∀ x, J.lab x = H.lab (e x))
    (E : Finset (Sym2 X)) (D : Finset (Finset X))
    (hD : IsDecomposition J F E D)
    (hPartition : edges J = E ∪ liftEdges f (edges Jnext))
    (hDisjoint : Disjoint E (liftEdges f (edges Jnext))) :
    p.paid ⊆ (p.append Jnext f hAdj hLab E D hD hPartition hDisjoint).paid := subset_union_left

theorem uncovered_eq {H : Host V I} {F : Set (Multiset I)}
    {reserved : Finset (Sym2 V)} {J : Host X I} {e : X ↪ V}
    (p : PaidPrefix H F reserved J e) :
    edges H \ p.paid.biUnion triEdges = reserved ∪ liftEdges e (edges J) := by
  rw [p.decomposition.2.2,p.partition]
  ext f
  rw [mem_sdiff,mem_union]
  constructor
  · rintro ⟨hPaid | hRest,hNot⟩
    · exact (hNot hPaid).elim
    · exact hRest
  · intro hRest
    exact ⟨Or.inr hRest,fun hPaid => disjoint_left.mp p.paid_disjoint hPaid hRest⟩

theorem uncovered_card_le {H : Host V I} {F : Set (Multiset I)}
    {reserved : Finset (Sym2 V)} {J : Host X I} {e : X ↪ V}
    (p : PaidPrefix H F reserved J e) (K : ℕ) (hK : reserved.card ≤ K) :
    (edges H \ p.paid.biUnion triEdges).card ≤ K+(Fintype.card X)^2 := by
  rw [p.uncovered_eq]
  calc
    _ ≤ reserved.card+(liftEdges e (edges J)).card := card_union_le _ _
    _ = reserved.card+(edges J).card := by rw [liftEdges,card_map]
    _ ≤ K+(Fintype.card X)^2 := Nat.add_le_add hK
      ((card_le_univ _).trans (sym2_card_le_square (V := X)))

#print axioms liftEdges_union
#print axioms liftEdges_comp
#print axioms liftEdges_mono
#print axioms liftEdges_disjoint
#print axioms append
#print axioms paid_subset_append
#print axioms uncovered_eq
#print axioms uncovered_card_le
end PaidPrefix
end TypedTriangle.Pasch

-- Source segment: PaschReservedTailCompletion.lean
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open Vortex Vortex.IntrinsicRawPathsPreparedVortex

theorem liftEdges_eq_embeddedEdges {X V : Type} (e : X ↪ V) (E : Finset (Sym2 X)) :
    AmbientBank.liftEdges e E = embeddedEdges e E := by
  unfold AmbientBank.liftEdges embeddedEdges
  rw [map_eq_image]
  rfl

/-- Complete the existing prepared suffix and absorb its terminal remainder,
retaining every block of the actual paid prefix. This reuses the proved tail
construction and its original terminal absorber contract. -/
theorem complete_reserved_tail_preserving_paid_prefix {I V Orig Abs : Type}
    [Fintype V] [Fintype Orig] [Fintype Abs]
    {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ}
    {h N M d T m : ℕ} {a εRoute t : ℝ} {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (Cactual αactual ζState : ℝ) (hLayers : LocalLayers chain Cactual αactual ζState)
    (state : ActualState chain Cactual αactual ζState)
    (HOrig : Host Orig I) (HAbs : Host Abs I)
    (eAbs : Survivors chain.head.trim ↪ Abs) (eOut : Abs ↪ Orig)
    (hAdjOrig : ∀ u v, state.host.G.Adj u v → HOrig.G.Adj (eOut (eAbs u)) (eOut (eAbs v)))
    (hLabOrig : ∀ u, state.host.lab u = HOrig.lab (eOut (eAbs u)))
    (hAdjAbs : ∀ u v, state.host.G.Adj u v → HAbs.G.Adj (eAbs u) (eAbs v))
    (hLabAbs : ∀ u, state.host.lab u = HAbs.lab (eAbs u))
    (hAdjOut : ∀ u v, HAbs.G.Adj u v → HOrig.G.Adj (eOut u) (eOut v))
    (hLabOut : ∀ u, HAbs.lab u = HOrig.lab (eOut u))
    (R : Finset (Sym2 Abs))
    (p : PaidPrefix HOrig F (embeddedEdges eOut R) state.host (eAbs.trans eOut))
    (hAbsorb : ∀ L : Finset (Sym2 Abs), Disjoint R L → IsPhysical HAbs F L →
      (∀ e ∈ L, ∀ v ∈ e, v ∈ chain.terminalWindow.map eAbs) → Basal HAbs F (R ∪ L)) :
    ∃ D : Finset (Finset Orig), IsDecomposition HOrig F (edges HOrig) D ∧ p.paid ⊆ D := by
  letI : DecidableEq (Survivors chain.head.trim) := Classical.decEq _
  have hEmpty : Basal HOrig F (p.paidEdges \ p.paidEdges) := by
    have hh : Basal HOrig F (∅ : Finset (Sym2 Orig)) := ⟨∅,by simp,by simp,by simp⟩
    simpa only [sdiff_self,bot_eq_empty] using hh
  have hPartition : edges HOrig = (p.paidEdges ∪ embeddedEdges eOut R) ∪
      embeddedEdges (eAbs.trans eOut) (edges state.host) := by
    rw [p.partition,liftEdges_eq_embeddedEdges]
    ac_rfl
  have hDisjoint : Disjoint p.paidEdges (embeddedEdges eOut R ∪
      embeddedEdges (eAbs.trans eOut) (edges state.host)) := by
    simpa only [liftEdges_eq_embeddedEdges] using p.paid_disjoint
  have hReserve : Disjoint (embeddedEdges eOut R)
      (embeddedEdges (eAbs.trans eOut) (edges state.host)) := by
    simpa only [liftEdges_eq_embeddedEdges] using p.reserve_child
  obtain ⟨P,L,hCP,hRest,hDis,hPart,hRL,hPhysical,hSupport,hLower,hUpper⟩ :=
    raw_paths_reserved_assembly_preserving_outer_cover chain Cactual αactual ζState hLayers state
      HOrig HAbs eAbs eOut hAdjOrig hLabOrig hAdjAbs hLabAbs p.paidEdges R p.paidEdges
      (subset_refl _) hEmpty hPartition hDisjoint hReserve
  exact decomposition_of_reserved_absorption_preserving HOrig HAbs F eOut hAdjOut hLabOut
    P p.paidEdges R L p.paid p.decomposition hCP hRest hDis hPart
    (hAbsorb L hRL hPhysical hSupport)

#print axioms liftEdges_eq_embeddedEdges
#print axioms complete_reserved_tail_preserving_paid_prefix
end TypedTriangle.Pasch

-- Source segment: PaschDepthPotential.lean
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace TypedTriangle.Pasch

def remainingPaschBudget (cost nRoot : ℝ) (j : ℕ) (nHost : ℝ) : ℝ :=
  2*cost*nRoot*(8 : ℝ)^j*nHost

theorem cubic_depth_le_eight_pow (j : ℕ) : ((j : ℝ)+1)^3 ≤ (8 : ℝ)^j := by
  have hj : (j : ℝ)+1 ≤ (2 : ℝ)^j := by exact_mod_cast depth_succ_le_two_pow j
  calc
    _ ≤ ((2 : ℝ)^j)^3 := pow_le_pow_left₀ (by positivity) hj 3
    _ = (8 : ℝ)^j := by rw [←pow_mul,Nat.mul_comm j 3,pow_mul]; norm_num

/-- One contraction pays both the actual new layer and the complete
remaining budget. This is suitable for induction on the prepared vortex. -/
theorem paid_step_and_remaining_budget (cost nRoot nHost nNext : ℝ) (j : ℕ)
    (hCost : 0 ≤ cost) (hnRoot : 0 ≤ nRoot) (hnHost : 0 ≤ nHost)
    (hShrink : 16*nNext ≤ nHost) :
    cost*nRoot*((j : ℝ)+1)^3*nHost + remainingPaschBudget cost nRoot (j+1) nNext ≤
      remainingPaschBudget cost nRoot j nHost := by
  have hCube := mul_le_mul_of_nonneg_right (cubic_depth_le_eight_pow j) hnHost
  have hPay := mul_le_mul_of_nonneg_left hCube (mul_nonneg hCost hnRoot)
  have hTail := mul_le_mul_of_nonneg_left hShrink
    (show (0 : ℝ) ≤ cost*nRoot*8^j by positivity)
  unfold remainingPaschBudget
  rw [pow_succ (8 : ℝ) j]
  nlinarith only [hPay,hTail]

theorem count_budget_preserved_by_paid_step (cost nRoot nHost nNext : ℝ) (j : ℕ)
    (oldCount newCount total : ℝ) (hCost : 0 ≤ cost) (hnRoot : 0 ≤ nRoot)
    (hnHost : 0 ≤ nHost) (hShrink : 16*nNext ≤ nHost)
    (hStep : newCount ≤ oldCount+cost*nRoot*((j : ℝ)+1)^3*nHost)
    (hBudget : oldCount+remainingPaschBudget cost nRoot j nHost ≤ total) :
    newCount+remainingPaschBudget cost nRoot (j+1) nNext ≤ total := by
  have hh := paid_step_and_remaining_budget cost nRoot nHost nNext j hCost hnRoot hnHost hShrink
  linarith only [hh,hStep,hBudget]

theorem initial_remaining_budget_le (cost nRoot q nHost : ℝ)
    (hCost : 0 ≤ cost) (hnRoot : 0 ≤ nRoot) (hFirst : nHost ≤ 2*q*nRoot) :
    remainingPaschBudget cost nRoot 0 nHost ≤ 4*cost*q*nRoot^2 := by
  have hh := mul_le_mul_of_nonneg_left hFirst (show (0 : ℝ) ≤ 2*cost*nRoot by positivity)
  calc
    _ = 2*cost*nRoot*nHost := by simp only [remainingPaschBudget,pow_zero,mul_one]
    _ ≤ 2*cost*nRoot*(2*q*nRoot) := hh
    _ = _ := by ring

#print axioms cubic_depth_le_eight_pow
#print axioms paid_step_and_remaining_budget
#print axioms count_budget_preserved_by_paid_step
#print axioms initial_remaining_budget_le
end TypedTriangle.Pasch

-- Source segment: PaschAdaptiveLayers.lean
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace TypedTriangle.Pasch
open Vortex Vortex.IntrinsicRawPathsPreparedVortex
variable {I Orig : Type} [Fintype Orig] {F : Set (Multiset I)}
  {α₀ q C : ℝ} {β : ℕ → ℝ} {h N M d T m : ℕ} {a εRoute t : ℝ}

/-- Intermediate interface for the concrete bank/resource/packing producer.
It retains the literal paid decomposition and the complete ambient mode
universe. The final host theorem must instantiate this interface. -/
def AdaptivePaidLayers {V : Type} [Fintype V] {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (Cactual αactual ζState : ℝ) (HOrig : Host Orig I)
    (cost : ℝ) (Lbase stepCodegree cutoff : ℕ) : Prop :=
  match chain with
  | .terminal _ _ => True
  | .descend node W lower shrink route paths intermediate next_index tail =>
      letI : DecidableEq (Survivors node.trim) := Classical.decEq _
      (∀ (state : ActualState (.descend node W lower shrink route paths intermediate next_index tail)
          Cactual αactual ζState)
        (e : Survivors node.trim ↪ Orig) (Rprev : Finset (Finset Orig)) (L j : ℕ),
        cutoff < Fintype.card (Survivors node.trim) →
        2^j*Fintype.card (Survivors node.trim) ≤ Fintype.card Orig →
        L ≤ Lbase+stepCodegree*j →
        (∀ x y, state.host.G.Adj x y → HOrig.G.Adj (e x) (e y)) →
        (∀ x, state.host.lab x = HOrig.lab (e x)) →
        PairCodegreeBound Rprev L → (∀ Q ∈ Rprev, Q.card = 3) →
        ∃ (child : ActualState tail Cactual αactual ζState)
          (E : Finset (Sym2 (Survivors node.trim)))
          (D : Finset (Finset (Survivors node.trim))) (Rnext : Finset (Finset Orig)),
          IsDecomposition state.host F E D ∧
          Disjoint E (AmbientBank.liftEdges (nextPreparedEmbedding W tail.head.trim) (edges child.host)) ∧
          edges state.host = E ∪
            AmbientBank.liftEdges (nextPreparedEmbedding W tail.head.trim) (edges child.host) ∧
          Rprev ⊆ Rnext ∧ mapConfiguration e D ⊆ Rnext ∧
          PairCodegreeBound Rnext (L+stepCodegree) ∧ (∀ Q ∈ Rnext, Q.card = 3) ∧
          (count Rnext : ℝ) ≤ count Rprev+
            cost*Fintype.card Orig*((j : ℝ)+1)^3*Fintype.card (Survivors node.trim)) ∧
        AdaptivePaidLayers tail Cactual αactual ζState HOrig cost Lbase stepCodegree cutoff

end TypedTriangle.Pasch

-- Source segment: PaschTrackingState.lean
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open Vortex Vortex.IntrinsicRawPathsPreparedVortex
variable {I V Orig Abs : Type} [Fintype V] [Fintype Orig] [Fintype Abs]
  {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ}
  {h N M d T m : ℕ} {a εRoute t : ℝ} {H : Host V I} {μ : Finset V → ℝ}

/-- Actual geometric state, literal paid prefix and ambient count budget
carried together through the controlled part of the prepared vortex. -/
structure TrackingState
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (Cactual αactual ζState : ℝ) (HOrig : Host Orig I) (HAbs : Host Abs I)
    (eOut : Abs ↪ Orig) (R : Finset (Sym2 Abs)) (base : Finset (Finset Orig))
    (Uterminal : Finset Abs) (cost τ : ℝ) (Lbase stepCodegree : ℕ) where
  actual : ActualState chain Cactual αactual ζState
  eAbs : Survivors chain.head.trim ↪ Abs
  prefixData : PaidPrefix HOrig F (embeddedEdges eOut R) actual.host (eAbs.trans eOut)
  available : Finset (Finset Orig)
  codegree : ℕ
  depth : ℕ
  pair_bound : PairCodegreeBound available codegree
  triples : ∀ Q ∈ available, Q.card = 3
  base_paid : base ⊆ prefixData.paid
  paid_available : prefixData.paid ⊆ available
  codegree_bound : codegree ≤ Lbase+stepCodegree*depth
  depth_bound : 2^depth*Fintype.card (Survivors chain.head.trim) ≤ Fintype.card Orig
  budget : (count available : ℝ)+remainingPaschBudget cost (Fintype.card Orig)
    depth (Fintype.card (Survivors chain.head.trim)) ≤ count base+τ*(Fintype.card Orig : ℝ)^2
  map_adj : ∀ u v, actual.host.G.Adj u v → HAbs.G.Adj (eAbs u) (eAbs v)
  map_lab : ∀ u, actual.host.lab u = HAbs.lab (eAbs u)
  terminal_subset : chain.terminalWindow.map eAbs ⊆ Uterminal

/-- At the cutoff, all future choices are made by the existing exact tail
assembly. The actual prefix and its original target are retained literally. -/
theorem TrackingState.complete_at_cutoff
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (Cactual αactual ζState : ℝ) (HOrig : Host Orig I) (HAbs : Host Abs I)
    (eOut : Abs ↪ Orig) (R : Finset (Sym2 Abs)) (base : Finset (Finset Orig))
    (Uterminal : Finset Abs) (cost τ σ targetValue : ℝ) (Lbase stepCodegree K : ℕ)
    (s : TrackingState chain Cactual αactual ζState HOrig HAbs eOut R base Uterminal cost τ Lbase stepCodegree)
    (hLayers : LocalLayers chain Cactual αactual ζState)
    (hAdjOut : ∀ u v, HAbs.G.Adj u v → HOrig.G.Adj (eOut u) (eOut v))
    (hLabOut : ∀ u, HAbs.lab u = HOrig.lab (eOut u))
    (hAbsorb : ∀ L : Finset (Sym2 Abs), Disjoint R L → IsPhysical HAbs F L →
      (∀ e ∈ L, ∀ v ∈ e, v ∈ Uterminal) → Basal HAbs F (R ∪ L))
    (hCost : 0 ≤ cost) (hτ : 0 < τ) (hn : 0 < Fintype.card Orig)
    (hK : R.card ≤ K)
    (hReserve : ⌈(K : ℝ)/τ⌉₊ ≤ Fintype.card Orig)
    (hSqrt : ⌈1/τ^2⌉₊ ≤ Fintype.card Orig)
    (hCut : Fintype.card (Survivors chain.head.trim) ≤ Nat.sqrt (Nat.sqrt (Fintype.card Orig)))
    (hTarget : |(count base : ℝ)-targetValue| ≤ σ*(Fintype.card Orig : ℝ)^2) :
    ∃ D : Finset (Finset Orig), IsDecomposition HOrig F (edges HOrig) D ∧ base ⊆ D ∧
      |(count D : ℝ)-targetValue| ≤ (σ+3*τ)*(Fintype.card Orig : ℝ)^2 := by
  have hAdjOrig : ∀ u v, s.actual.host.G.Adj u v →
      HOrig.G.Adj (eOut (s.eAbs u)) (eOut (s.eAbs v)) :=
    fun u v huv => hAdjOut _ _ (s.map_adj u v huv)
  have hLabOrig : ∀ u, s.actual.host.lab u = HOrig.lab (eOut (s.eAbs u)) :=
    fun u => (s.map_lab u).trans (hLabOut _)
  obtain ⟨D,hD,hPaidD⟩ := complete_reserved_tail_preserving_paid_prefix chain Cactual αactual ζState
    hLayers s.actual HOrig HAbs s.eAbs eOut hAdjOrig hLabOrig s.map_adj s.map_lab hAdjOut hLabOut
    R s.prefixData (fun L hRL hPhys hSupport => hAbsorb L hRL hPhys
      (fun e he v hv => s.terminal_subset (hSupport e he v hv)))
  have hRemain : 0 ≤ remainingPaschBudget cost (Fintype.card Orig) s.depth
      (Fintype.card (Survivors chain.head.trim)) := by unfold remainingPaschBudget; positivity
  have hCount : (count s.available : ℝ) ≤ count base+τ*(Fintype.card Orig : ℝ)^2 := by
    have hh := s.budget
    linarith only [hh,hRemain]
  have hPaidTarget := adaptive_sandwich_target_error base s.available s.prefixData.paid targetValue σ τ
    (τ*(Fintype.card Orig : ℝ)^2) s.base_paid s.paid_available hCount (by positivity) le_rfl hTarget
  have hPaid : IsPacking HOrig F s.prefixData.paid :=
    ⟨s.prefixData.decomposition.1,s.prefixData.decomposition.2.1⟩
  have hR : (embeddedEdges eOut R).card ≤ K := (card_image_le).trans hK
  have hRest := s.prefixData.uncovered_card_le K hR
  have hError := small_remainder_completion_target_error hPaid hD hPaidD K
    (Fintype.card (Survivors chain.head.trim)) τ (σ+τ) targetValue hτ hn hCut hReserve hSqrt hRest hPaidTarget
  refine ⟨D,hD,s.base_paid.trans hPaidD,?_⟩
  convert hError using 1 <;> ring

#print axioms TrackingState.complete_at_cutoff
end TypedTriangle.Pasch

-- Source segment: PaschTrackingStep.lean
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open Vortex Vortex.IntrinsicRawPathsPreparedVortex
variable {I V X Orig Abs : Type} [Fintype V] [Fintype X] [Fintype Orig] [Fintype Abs]
  {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ}
  {h N M d T m : ℕ} {a εRoute t : ℝ}
  {H : Host V I} {μ : Finset V → ℝ} {J : Host X I} {ν : Finset X → ℝ}

theorem paid_partition_change_decEq {X I : Type} [Fintype X]
    (H : Host X I) (A B : Finset (Sym2 X)) (d₁ d₂ : DecidableEq (Sym2 X))
    (hEq : edges H = @Union.union _ (@Finset.instUnion _ d₁) A B) :
    edges H = @Union.union _ (@Finset.instUnion _ d₂) A B := by
  cases Subsingleton.elim d₁ d₂
  exact hEq

/-- A concrete paid step updates the exact partition, ambient universe,
pair codegree and remaining count budget in one state. -/
@[irreducible] def TrackingState.advance
    (parent : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (tail : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t J ν)
    (Cactual αactual ζState : ℝ) (HOrig : Host Orig I) (HAbs : Host Abs I)
    (eOut : Abs ↪ Orig) (R : Finset (Sym2 Abs)) (base : Finset (Finset Orig))
    (Uterminal : Finset Abs) (cost τ : ℝ) (Lbase stepCodegree : ℕ)
    (s : TrackingState parent Cactual αactual ζState HOrig HAbs eOut R base Uterminal cost τ Lbase stepCodegree)
    (child : ActualState tail Cactual αactual ζState)
    (f : Survivors tail.head.trim ↪ Survivors parent.head.trim)
    (hAdjOut : ∀ u v, HAbs.G.Adj u v → HOrig.G.Adj (eOut u) (eOut v))
    (hLabOut : ∀ u, HAbs.lab u = HOrig.lab (eOut u))
    (hAdj : ∀ u v, child.host.G.Adj u v → s.actual.host.G.Adj (f u) (f v))
    (hLab : ∀ u, child.host.lab u = s.actual.host.lab (f u))
    (hShrink : 16*Fintype.card (Survivors tail.head.trim) ≤ Fintype.card (Survivors parent.head.trim))
    (hTerminal : parent.terminalWindow = tail.terminalWindow.map f)
    (E : Finset (Sym2 (Survivors parent.head.trim)))
    (D : Finset (Finset (Survivors parent.head.trim))) (Rnext : Finset (Finset Orig))
    (hD : IsDecomposition s.actual.host F E D)
    (hDisjoint : Disjoint E (AmbientBank.liftEdges f (edges child.host)))
    (hPartition :
      letI : DecidableEq (Survivors parent.head.trim) := Classical.decEq _
      edges s.actual.host = E ∪ AmbientBank.liftEdges f (edges child.host))
    (hOldNew : s.available ⊆ Rnext)
    (hPaidNew : mapConfiguration (s.eAbs.trans eOut) D ⊆ Rnext)
    (hPair : PairCodegreeBound Rnext (s.codegree+stepCodegree))
    (hTriples : ∀ Q ∈ Rnext, Q.card = 3)
    (hStep : (count Rnext : ℝ) ≤ count s.available+
      cost*Fintype.card Orig*((s.depth : ℝ)+1)^3*Fintype.card (Survivors parent.head.trim))
    (hCost : 0 ≤ cost) :
    TrackingState tail Cactual αactual ζState HOrig HAbs eOut R base Uterminal cost τ Lbase stepCodegree := by
  have hAdjOrig : ∀ u v, s.actual.host.G.Adj u v →
      HOrig.G.Adj ((s.eAbs.trans eOut) u) ((s.eAbs.trans eOut) v) :=
    fun u v huv => hAdjOut _ _ (s.map_adj u v huv)
  have hLabOrig : ∀ u, s.actual.host.lab u = HOrig.lab ((s.eAbs.trans eOut) u) :=
    fun u => (s.map_lab u).trans (hLabOut _)
  have hPartition' :
      letI : DecidableEq (Survivors parent.head.trim) := Classical.decEq _
      edges s.actual.host = E ∪ AmbientBank.liftEdges f (edges child.host) := by
    letI : DecidableEq (Survivors parent.head.trim) := Classical.decEq _
    exact paid_partition_change_decEq s.actual.host E
      (AmbientBank.liftEdges f (edges child.host)) _ _ hPartition
  let p : PaidPrefix HOrig F (embeddedEdges eOut R) child.host ((f.trans s.eAbs).trans eOut) :=
    PaidPrefix.append (H := HOrig) (F := F) (reserved := embeddedEdges eOut R)
      (J := s.actual.host) (e := s.eAbs.trans eOut) s.prefixData child.host f
      hAdjOrig hLabOrig E D hD hPartition' hDisjoint
  refine {
    actual := child
    eAbs := f.trans s.eAbs
    prefixData := p
    available := Rnext
    codegree := s.codegree+stepCodegree
    depth := s.depth+1
    pair_bound := hPair
    triples := hTriples
    base_paid := ?_
    paid_available := ?_
    codegree_bound := ?_
    depth_bound := ?_
    budget := ?_
    map_adj := fun u v huv => s.map_adj (f u) (f v) (hAdj u v huv)
    map_lab := fun u => (hLab u).trans (s.map_lab (f u))
    terminal_subset := ?_
  }
  · change base ⊆ s.prefixData.paid ∪ mapConfiguration (s.eAbs.trans eOut) D
    exact s.base_paid.trans subset_union_left
  · change s.prefixData.paid ∪ mapConfiguration (s.eAbs.trans eOut) D ⊆ Rnext
    exact union_subset (s.paid_available.trans hOldNew) hPaidNew
  · have hh := s.codegree_bound
    nlinarith only [hh]
  · have hTwo : 2*Fintype.card (Survivors tail.head.trim) ≤
        Fintype.card (Survivors parent.head.trim) := by omega
    calc
      _ = 2^s.depth*(2*Fintype.card (Survivors tail.head.trim)) := by rw [pow_succ]; ring
      _ ≤ 2^s.depth*Fintype.card (Survivors parent.head.trim) := Nat.mul_le_mul_left _ hTwo
      _ ≤ Fintype.card Orig := s.depth_bound
  · have hShrinkR : 16*(Fintype.card (Survivors tail.head.trim) : ℝ) ≤
        (Fintype.card (Survivors parent.head.trim) : ℝ) := by exact_mod_cast hShrink
    exact count_budget_preserved_by_paid_step cost (Fintype.card Orig)
      (Fintype.card (Survivors parent.head.trim)) (Fintype.card (Survivors tail.head.trim))
      s.depth (count s.available) (count Rnext) (count base+τ*(Fintype.card Orig : ℝ)^2)
      hCost (by positivity) (by positivity) hShrinkR hStep s.budget
  · have hEq : tail.terminalWindow.map (f.trans s.eAbs) = parent.terminalWindow.map s.eAbs := by
      rw [hTerminal,map_map]
    rw [hEq]
    exact s.terminal_subset

#print axioms TrackingState.advance
end TypedTriangle.Pasch

-- Source segment: PaschDepthEligibility.lean
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch

theorem embedded_degree_scale_quadratic (C : ℝ) (L : ℕ) (hC : 0 ≤ C) :
    6*C^3+localMixedDegreeScale C L ≤
      (6*C^3+localMixedDegreeScale C 1)*((L+1 : ℕ) : ℝ)^2 := by
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have h1 : (1 : ℝ) ≤ ((L+1 : ℕ) : ℝ)^2 := by push_cast; nlinarith only [hL0,sq_nonneg (L : ℝ)]
  have hL : (L : ℝ) ≤ ((L+1 : ℕ) : ℝ)^2 := by push_cast; nlinarith only [hL0,sq_nonneg (L : ℝ)]
  have hL2 : (L : ℝ)^2 ≤ ((L+1 : ℕ) : ℝ)^2 := by push_cast; nlinarith only [hL0]
  have hConst := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 6*C^3+2*C+3 by positivity)
  have hLinear := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 6*C^2+9 by positivity)
  have hQuadratic := mul_le_mul_of_nonneg_left hL2 (show (0 : ℝ) ≤ 27+27*C by positivity)
  unfold localMixedDegreeScale mixedDegreeScale
  norm_num only [Nat.cast_one,one_pow,mul_one] at *
  nlinarith only [hConst,hLinear,hQuadratic]

def embeddedEligibilityDepthCoefficient (α C : ℝ) (Lbase stepCodegree : ℕ) : ℕ :=
  max (max (supersaturationOrder α) ⌈2*C⌉₊)
    ⌈((6*C^3+localMixedDegreeScale C 1)/(massConstant α C/16))^2*
      ((Lbase+stepCodegree+1 : ℕ) : ℝ)^4⌉₊

theorem embedded_eligibility_order_quartic_depth (α C : ℝ) (hα : 0 < α) (hC : 1 ≤ C)
    (Lbase stepCodegree L j : ℕ) (hL : L ≤ Lbase+stepCodegree*j) :
    embeddedMixedEligibilityOrder α C L ≤
      embeddedEligibilityDepthCoefficient α C Lbase stepCodegree*(j+1)^4 := by
  let c := massConstant α C/16
  let G := 6*C^3+localMixedDegreeScale C 1
  let A := embeddedEligibilityDepthCoefficient α C Lbase stepCodegree
  let M := Lbase+stepCodegree+1
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hc : 0 < c := by dsimp only [c,massConstant]; positivity
  have hG : 0 ≤ G := by dsimp only [G,localMixedDegreeScale,mixedDegreeScale]; positivity
  have hGL : 0 ≤ 6*C^3+localMixedDegreeScale C L := by
    unfold localMixedDegreeScale mixedDegreeScale
    positivity
  have hLM : L+1 ≤ M*(j+1) := by
    dsimp only [M]
    nlinarith only [hL,Nat.zero_le (Lbase*j)]
  have hLMR : ((L+1 : ℕ) : ℝ) ≤ (M : ℝ)*(j+1) := by exact_mod_cast hLM
  have hSquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (L+1 : ℕ)) hLMR 2
  have hGamma := (embedded_degree_scale_quadratic C L hC0.le).trans
    (mul_le_mul_of_nonneg_left hSquare hG)
  have hRatio : (6*C^3+localMixedDegreeScale C L)/c ≤ (G/c)*((M : ℝ)*(j+1))^2 := by
    convert div_le_div_of_nonneg_right hGamma hc.le using 1 <;> dsimp only [G] <;> ring
  have hPower := pow_le_pow_left₀ (div_nonneg hGL hc.le) hRatio 2
  have hCoeff : (G/c)^2*(M : ℝ)^4 ≤ (A : ℝ) := by
    have hCeil : ⌈(G/c)^2*(M : ℝ)^4⌉₊ ≤ A := by
      dsimp only [A,embeddedEligibilityDepthCoefficient,G,c,M]
      exact le_max_right _ _
    exact (Nat.le_ceil _).trans (by exact_mod_cast hCeil)
  have hPay := mul_le_mul_of_nonneg_right hCoeff (show (0 : ℝ) ≤ ((j : ℝ)+1)^4 by positivity)
  have hCutoff : ⌈((6*C^3+localMixedDegreeScale C L)/c)^2⌉₊ ≤ A*(j+1)^4 := by
    apply Nat.ceil_le.mpr
    calc
      _ ≤ ((G/c)*((M : ℝ)*(j+1))^2)^2 := hPower
      _ = ((G/c)^2*(M : ℝ)^4)*((j : ℝ)+1)^4 := by ring
      _ ≤ (A : ℝ)*((j : ℝ)+1)^4 := hPay
      _ = _ := by push_cast; ring
  have hFloor : max (supersaturationOrder α) ⌈2*C⌉₊ ≤ A := by
    dsimp only [A,embeddedEligibilityDepthCoefficient]
    exact le_max_left _ _
  have hOne : 1 ≤ (j+1)^4 := one_le_pow₀ (by omega : 1 ≤ j+1)
  change max (max (supersaturationOrder α) ⌈2*C⌉₊)
    ⌈((6*C^3+localMixedDegreeScale C L)/c)^2⌉₊ ≤ A*(j+1)^4
  exact max_le (hFloor.trans (le_mul_of_one_le_right (Nat.zero_le _) hOne)) hCutoff

/-- A single explicit initial order discharges all embedded mixed tests
at every actual tracked depth, before the fourth-root cutoff. -/
theorem embedded_mixed_order_below_tracking_cutoff (α C : ℝ) (hα : 0 < α) (hC : 1 ≤ C)
    (Lbase stepCodegree L j nRoot nHost : ℕ) (hL : L ≤ Lbase+stepCodegree*j)
    (hOrder : paschDepthOrder (embeddedEligibilityDepthCoefficient α C Lbase stepCodegree) ≤ nRoot)
    (hDepth : 2^j*nHost ≤ nRoot) (hTracking : Nat.sqrt (Nat.sqrt nRoot) < nHost) :
    embeddedMixedEligibilityOrder α C L ≤ nHost := by
  have hPow : 2^j ≤ nRoot :=
    (le_mul_of_one_le_right (Nat.zero_le _) (by omega : 1 ≤ nHost)).trans hDepth
  have hj : j ≤ Nat.log 2 nRoot := Nat.le_log_of_pow_le (by decide) hPow
  exact (embedded_eligibility_order_quartic_depth α C hα hC Lbase stepCodegree L j hL).trans
    ((quartic_log_bound_at_explicit_order _ nRoot j hOrder hj).trans hTracking.le)

#print axioms embedded_degree_scale_quadratic
#print axioms embedded_eligibility_order_quartic_depth
#print axioms embedded_mixed_order_below_tracking_cutoff
end TypedTriangle.Pasch
