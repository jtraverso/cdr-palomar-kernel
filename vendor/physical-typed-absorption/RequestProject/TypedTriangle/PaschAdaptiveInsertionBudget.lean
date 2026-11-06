module
public import RequestProject.TypedTriangle.PaschAdaptiveAssemblyCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch

/-- The quadratic child exception coefficient is bounded by the same
cubic codegree scale as the ambient one-new-block monitor. -/
theorem child_exception_coefficient_le_cubic {C : ℝ} (hC : 0 ≤ C) (L : ℕ) :
    2*(6*(L : ℝ)*C^2+C^3)*(L : ℝ)+5*C^3 ≤
      (12*C^2+7*C^3)*((L+1 : ℕ) : ℝ)^3 := by
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hL3 : (0 : ℝ) ≤ (L : ℝ)^2*(L : ℝ) := mul_nonneg (sq_nonneg _) hL0
  have hOne : (1 : ℝ) ≤ ((L+1 : ℕ) : ℝ)^3 := by
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ L+1 by omega))
  have hLinear : (L : ℝ) ≤ ((L+1 : ℕ) : ℝ)^3 := by
    push_cast
    nlinarith only [hL0,hL3,sq_nonneg (L : ℝ)]
  have hSquare : (L : ℝ)^2 ≤ ((L+1 : ℕ) : ℝ)^3 := by
    push_cast
    nlinarith only [hL0,hL3,sq_nonneg (L : ℝ)]
  have hA := mul_le_mul_of_nonneg_left hSquare
    (show (0 : ℝ) ≤ 12*C^2 by positivity)
  have hB := mul_le_mul_of_nonneg_left hLinear
    (show (0 : ℝ) ≤ 2*C^3 by positivity)
  have hD := mul_le_mul_of_nonneg_left hOne
    (show (0 : ℝ) ≤ 5*C^3 by positivity)
  nlinarith only [hA,hB,hD]

/-- Pure, ambient-linear and child-exception controls on the same actual
packing pay for insertion into the full previous ambient universe. -/
theorem embedded_insertion_count_le {X V : Type*} [Fintype X] [Fintype V]
    (e : X ↪ V) (P : Finset (Finset X)) (R : Finset (Finset V)) (L : ℕ)
    (C pure monitor : ℝ) (hC : 0 ≤ C) (hPure0 : 0 ≤ pure) (hMonitor0 : 0 ≤ monitor)
    (hnRoot : 0 < Fintype.card V)
    (hPure : (count P : ℝ) ≤ pure*(Fintype.card X : ℝ)^2)
    (hMonitor : (∑ T ∈ P, childPaddedWeight e R L T) ≤ monitor*Fintype.card X)
    (hExceptions :
      PatternStatistics.statistic
        (completionWeight (childExceptions R ((univ : Finset X).map e))) 2 (mapConfiguration e P)+
      PatternStatistics.statistic
        (completionWeight (childExceptions R ((univ : Finset X).map e))) 3 (mapConfiguration e P) ≤
      (2*(6*(L : ℝ)*C^2+C^3)*(L : ℝ)+5*C^3)*(Fintype.card X : ℝ)^2) :
    (count (mapConfiguration e P ∪ R) : ℝ) ≤ count R+
      (pure+2*monitor+12*C^2+7*C^3)*((L+1 : ℕ) : ℝ)^3*
        Fintype.card V*Fintype.card X := by
  let n := (Fintype.card X : ℝ)
  let nRoot := (Fintype.card V : ℝ)
  let J := ((L+1 : ℕ) : ℝ)^3
  let E := 2*(6*(L : ℝ)*C^2+C^3)*(L : ℝ)+5*C^3
  let D := 12*C^2+7*C^3
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hRoot0 : 0 ≤ nRoot := Nat.cast_nonneg _
  have hJ1 : 1 ≤ J := by
    dsimp only [J]
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ L+1 by omega))
  have hJ0 : 0 ≤ J := le_trans (by norm_num) hJ1
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hHostRoot : n ≤ nRoot := by
    dsimp only [n,nRoot]
    exact_mod_cast (Fintype.card_le_of_injective e e.injective)
  have hSq : n^2 ≤ nRoot*n := by
    have hh := mul_le_mul_of_nonneg_right hHostRoot hn0
    nlinarith only [hh]
  have hPurePaid : pure*n^2 ≤ pure*J*nRoot*n := by
    have hA := mul_le_mul_of_nonneg_left hSq hPure0
    have hB := mul_le_mul_of_nonneg_right hJ1
      (show 0 ≤ pure*nRoot*n by positivity)
    nlinarith only [hA,hB]
  have hExceptionPaid : E*n^2 ≤ D*J*nRoot*n := by
    have hE := child_exception_coefficient_le_cubic hC L
    change E ≤ D*J at hE
    have hA := mul_le_mul_of_nonneg_right hE (sq_nonneg n)
    have hB := mul_le_mul_of_nonneg_left hSq (mul_nonneg hD0 hJ0)
    nlinarith only [hA,hB]
  have hCount := embedded_packing_union_count_increment e P R L
    (monitor*Fintype.card X) hnRoot hMonitor
  change (count P : ℝ) ≤ pure*n^2 at hPure
  change _ ≤ E*n^2 at hExceptions
  change (count (mapConfiguration e P ∪ R) : ℝ) ≤ count R+count P+
    2*nRoot*J*(monitor*n)+_+_ at hCount
  calc
    _ ≤ count R+pure*n^2+2*nRoot*J*(monitor*n)+E*n^2 := by
      linarith only [hCount,hPure,hExceptions]
    _ ≤ count R+pure*J*nRoot*n+2*nRoot*J*(monitor*n)+D*J*nRoot*n := by
      linarith only [hPurePaid,hExceptionPaid]
    _ = _ := by dsimp only [D,J,nRoot,n]; ring

/-- Affine growth of pair codegree is absorbed into one fixed cubic
coefficient. All shifts are natural numbers; in particular this covers s≥1. -/
theorem affine_codegree_shift_cube_le (L Lbase K j s : ℕ)
    (hL : L ≤ Lbase+K*j) :
    ((L+s : ℕ) : ℝ)^3 ≤ ((Lbase+K+s : ℕ) : ℝ)^3*((j+1 : ℕ) : ℝ)^3 := by
  have hNat : L+s ≤ (Lbase+K+s)*(j+1) := by
    nlinarith only [hL,Nat.zero_le (Lbase*j),Nat.zero_le K,Nat.zero_le (s*j)]
  have hReal : ((L+s : ℕ) : ℝ) ≤ ((Lbase+K+s : ℕ) : ℝ)*((j+1 : ℕ) : ℝ) := by
    exact_mod_cast hNat
  calc
    _ ≤ (((Lbase+K+s : ℕ) : ℝ)*((j+1 : ℕ) : ℝ))^3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hReal 3
    _ = _ := mul_pow _ _ _

theorem insertion_cost_shift_le_uniform (Dgeom : ℝ) (hDgeom : 0 ≤ Dgeom)
    (L Lbase K j s : ℕ) (hL : L ≤ Lbase+K*j) :
    Dgeom*((L+s : ℕ) : ℝ)^3 ≤
      (Dgeom*((Lbase+K+s : ℕ) : ℝ)^3)*((j+1 : ℕ) : ℝ)^3 := by
  have hh := mul_le_mul_of_nonneg_left (affine_codegree_shift_cube_le L Lbase K j s hL) hDgeom
  exact hh.trans_eq (by ring)

#print axioms child_exception_coefficient_le_cubic
#print axioms embedded_insertion_count_le
#print axioms affine_codegree_shift_cube_le
#print axioms insertion_cost_shift_le_uniform
end TypedTriangle.Pasch
