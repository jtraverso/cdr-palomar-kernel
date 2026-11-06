module
public import RequestProject.TypedTriangle.PaschAmbientNativeBank
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch

/-- The geometric support cost is exactly cubic in the previous pair codegree. -/
theorem absorptionPotentialCost_cubic (α : ℝ) (h Ub L : ℕ) :
    absorptionPotentialCost α h Ub L = (L:ℝ)^3*absorptionPotentialCost α h Ub 1 := by
  unfold absorptionPotentialCost gadgetPotentialCost compositePotentialCost hingePotentialCost
  simp only [Nat.cast_one,one_pow,div_eq_mul_inv]
  ring

private theorem cubic_dominates_linear_tail (A B D : ℝ) (hB : 0≤B) (hD : 0≤D)
    (L : ℕ) (hL : 1≤L) :
    A*(L:ℝ)^3+B*(L:ℝ)+D ≤ (L:ℝ)^3*(A+B+D) := by
  have hLr : (1:ℝ)≤L := by exact_mod_cast hL
  have hSquare : (1:ℝ)≤(L:ℝ)^2 := by nlinarith only [hLr,sq_nonneg ((L:ℝ)-1)]
  have hCube : (L:ℝ)≤(L:ℝ)^3 := by
    have hh := mul_le_mul_of_nonneg_left hSquare (by positivity : (0:ℝ)≤L)
    nlinarith only [hh]
  have hOne : (1:ℝ)≤(L:ℝ)^3 := hLr.trans hCube
  have hLinear := mul_le_mul_of_nonneg_right hCube hB
  have hConstant := mul_le_mul_of_nonneg_right hOne hD
  nlinarith only [hLinear,hConstant]

/-- No host or compression witness enters the cubic factor. -/
theorem catalogCellPotentialCost_cubic_le (α β : ℝ) (h d c E d' c' E' L : ℕ)
    (hL : 1≤L) :
    catalogCellPotentialCost α β h d c E d' c' E' L ≤
      (L:ℝ)^3*catalogCellPotentialCost α β h d c E d' c' E' 1 := by
  let k := 4*S07V42.Explicit.rerouteSize β d c E d' c' E'
  let K := ExplicitCertificate.uniformCertCost (α/2) h
  let Ub := weightedCatalogSupport α β h d c E d' c' E'
  let A : ℝ := ((K*k:ℕ):ℝ)*absorptionPotentialCost α h Ub 1
  let B : ℝ := 9*((Ub.choose 3).choose 2:ℝ)
  let D : ℝ := ((Ub.choose 3).choose 3:ℝ)+((Ub.choose 3).choose 4:ℝ)
  have hCost (l : ℕ) : catalogCellPotentialCost α β h d c E d' c' E' l =
      A*(l:ℝ)^3+B*(l:ℝ)+D := by
    unfold catalogCellPotentialCost
    dsimp only
    rw [absorptionPotentialCost_cubic]
    dsimp only [A,B,D,k,K,Ub]
    push_cast
    ring
  rw [hCost L,hCost 1]
  simp only [Nat.cast_one,one_pow,mul_one]
  exact cubic_dominates_linear_tail A B D (by dsimp [B]; positivity)
    (by dsimp [D]; positivity) L hL

/-- The ambient/local ratio is retained exactly, including for growing L0. -/
theorem ambient_catalogCellPotentialCost_cubic_le
    {X V : Type*} [Fintype X] [Fintype V] (ι : X ↪ V)
    (α β : ℝ) (h d c E d' c' E' L : ℕ) (hL : 1≤L) :
    Ambient.orderRatio ι*catalogCellPotentialCost α β h d c E d' c' E' L ≤
      (L:ℝ)^3*(Ambient.orderRatio ι*catalogCellPotentialCost α β h d c E d' c' E' 1) := by
  have hh := mul_le_mul_of_nonneg_left
    (catalogCellPotentialCost_cubic_le α β h d c E d' c' E' L hL)
    (Ambient.orderRatio_nonneg ι)
  convert hh using 1 <;> ring

theorem ambient_catalogCellPotentialCost_seeded_le
    {X V : Type*} [Fintype X] [Fintype V] (ι : X ↪ V)
    (α β : ℝ) (h d c E d' c' E' L0 : ℕ) :
    Ambient.orderRatio ι*catalogCellPotentialCost α β h d c E d' c' E' (L0+2) ≤
      ((L0+2:ℕ):ℝ)^3*(Ambient.orderRatio ι*catalogCellPotentialCost α β h d c E d' c' E' 1) :=
  ambient_catalogCellPotentialCost_cubic_le ι α β h d c E d' c' E' (L0+2) (by omega)

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.absorptionPotentialCost_cubic
#print axioms TypedTriangle.Pasch.catalogCellPotentialCost_cubic_le
#print axioms TypedTriangle.Pasch.ambient_catalogCellPotentialCost_cubic_le
#print axioms TypedTriangle.Pasch.ambient_catalogCellPotentialCost_seeded_le
