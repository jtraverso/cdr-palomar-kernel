module
public import RequestProject.TypedTriangle.PaschDenseWeightedWithdrawal
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open CorePaid.Explicit

def withdrawalRouteTail (m : ℕ) : ℕ :=
  9*(m+1).choose 2+(m+1).choose 3+(m+1).choose 4

def withdrawalRouteCoefficient (a : ℝ) (m : ℕ) : ℝ :=
  200*(((m+1:ℕ):ℝ)/(a/(2:ℝ)^(m+3))+(withdrawalRouteTail m:ℝ))

def withdrawalGeometryCost (κ q a : ℝ) (m : ℕ) : ℝ :=
  let K := forkQLimit κ+6
  let D := selQLimit (Vortex.windowRouteRate a q m) (S07V27.selA (m+1))
  12/κ+4*(K:ℝ)/q*withdrawalRouteCoefficient a m+
    2*((61*K+60*D*(K+1):ℕ):ℝ)/κ

def withdrawalRawPayment (κ a : ℝ) (m L nAmbient nHost w roots r1 z qSel : ℕ) : ℝ :=
  (roots:ℝ)*forkPaschPayment κ L nAmbient nHost+
    ((r1*z:ℕ):ℝ)*weightedCoreRoutePay a m nAmbient w (L+122)+
    2*((61*r1+60*qSel:ℕ):ℝ)*nAmbient*((L+63:ℕ):ℝ)^3/κ

theorem withdrawalGeometryCost_pos {κ q a : ℝ} (m : ℕ)
    (hκ : 0 < κ) (hq : 0 < q) (ha : 0 < a) :
    0 < withdrawalGeometryCost κ q a m := by
  unfold withdrawalGeometryCost withdrawalRouteCoefficient
  positivity

private theorem route_payment_le_coefficient {a : ℝ} (ha : 0 < a)
    (m L nAmbient w : ℕ) (hw : 0 < (w:ℝ)) (hAw : w ≤ nAmbient) :
    weightedCoreRoutePay a m nAmbient w (L+122) ≤
      ((nAmbient:ℝ)/w)*withdrawalRouteCoefficient a m*((L+182:ℕ):ℝ)^3 := by
  let J : ℝ := ((L+182:ℕ):ℝ)
  have hJ : 1 ≤ J := by dsimp only [J]; exact_mod_cast (show 1 ≤ L+182 by omega)
  have hJ0 : 0 ≤ J := le_trans (by norm_num) hJ
  have hJ3 : 1 ≤ J^3 := one_le_pow₀ hJ
  have hJle : J ≤ J^3 := by
    calc J=J*1 := (mul_one J).symm
         _ ≤ J*J^2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hJ) hJ0
         _=J^3 := by ring
  have hRatio : 1 ≤ (nAmbient:ℝ)/w := by
    apply (le_div_iff₀ hw).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr hAw : (w:ℝ) ≤ nAmbient)
  have hA := mul_le_mul_of_nonneg_left hJle
    (show 0 ≤ 9*((m+1).choose 2:ℝ) by positivity)
  have hB := mul_le_mul_of_nonneg_left hJ3
    (show 0 ≤ ((m+1).choose 3:ℝ)+(m+1).choose 4 by positivity)
  have hTail : 9*J*((m+1).choose 2:ℝ)+(m+1).choose 3+(m+1).choose 4 ≤
      (withdrawalRouteTail m:ℝ)*J^3 := by
    unfold withdrawalRouteTail
    push_cast
    nlinarith only [hA,hB]
  have hTailRatio := mul_le_mul_of_nonneg_right hRatio
    (show 0 ≤ (withdrawalRouteTail m:ℝ)*J^3 by positivity)
  have hTail' : 9*J*((m+1).choose 2:ℝ)+(m+1).choose 3+(m+1).choose 4 ≤
      ((nAmbient:ℝ)/w)*(withdrawalRouteTail m:ℝ)*J^3 := by
    calc _ ≤ (withdrawalRouteTail m:ℝ)*J^3 := hTail
         _ ≤ ((nAmbient:ℝ)/w)*((withdrawalRouteTail m:ℝ)*J^3) := by simpa only [one_mul] using hTailRatio
         _=_ := by ring
  have hShift : L+122+60=L+182 := by omega
  unfold weightedCoreRoutePay ambientWeightedRoutePayment withdrawalRouteCoefficient
  rw [hShift]
  push_cast
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (((nAmbient:ℝ)/w)*(((m+1:ℕ):ℝ)*J^3)/(a/(2:ℝ)^(m+3)))) hTail')
    (show (0:ℝ) ≤ 200 by norm_num)
  convert hh using 1 <;> dsimp only [J] <;> push_cast <;> ring

/-- A bound for the complete fixed universe, including every fork mode,
all selector candidates and the literal common H3 payment. Its coefficient
contains no stock supply or thinning parameter. -/
theorem withdrawal_raw_payment_le_uniform {κ q a : ℝ} (m : ℕ)
    (hκ : 0 < κ) (hq : 0 < q) (ha : 0 < a)
    (L nAmbient nHost w roots r r1 z qSel : ℕ)
    (hn : 0 < nHost) (hAw : w ≤ nAmbient)
    (hW : q*(nHost:ℝ)/4 ≤ w)
    (hRoots : (roots:ℝ) ≤ (nHost:ℝ)*r/2)
    (hz : z ≤ nHost)
    (hR1 : r1 ≤ (forkQLimit κ+6)*(r+1))
    (hQ : qSel ≤ selQLimit (Vortex.windowRouteRate a q m) (S07V27.selA (m+1))*
      (forkQLimit κ+6+1)*(r+1)) :
    withdrawalRawPayment κ a m L nAmbient nHost w roots r1 z qSel ≤
      withdrawalGeometryCost κ q a m*(r+1)*nAmbient*((L+182:ℕ):ℝ)^3 := by
  let K := forkQLimit κ+6
  let D := selQLimit (Vortex.windowRouteRate a q m) (S07V27.selA (m+1))
  let J : ℝ := ((L+182:ℕ):ℝ)
  have hnR : 0 < (nHost:ℝ) := Nat.cast_pos.mpr hn
  have hw : 0 < (w:ℝ) := lt_of_lt_of_le (by positivity) hW
  have hNw : (nHost:ℝ)/w ≤ 4/q := by
    apply (div_le_div_iff₀ hw hq).mpr
    nlinarith only [hW]
  have hJ0 : 0 ≤ J := by dsimp only [J]; positivity
  have hCube4 : ((L+4:ℕ):ℝ)^3 ≤ J^3 :=
    pow_le_pow_left₀ (by positivity) (by dsimp only [J]; exact_mod_cast (show L+4 ≤ L+182 by omega)) 3
  have hCube63 : ((L+63:ℕ):ℝ)^3 ≤ J^3 :=
    pow_le_pow_left₀ (by positivity) (by dsimp only [J]; exact_mod_cast (show L+63 ≤ L+182 by omega)) 3
  have hFork0 := mul_le_mul_of_nonneg_right hRoots (forkPaschPayment_nonneg hκ L nAmbient nHost)
  have hForkEq : ((nHost:ℝ)*r/2)*forkPaschPayment κ L nAmbient nHost=
      (12/κ)*(r:ℝ)*nAmbient*((L+4:ℕ):ℝ)^3 := by
    unfold forkPaschPayment
    field_simp [ne_of_gt hnR,ne_of_gt hκ] <;> ring
  rw [hForkEq] at hFork0
  have hFork1 := mul_le_mul_of_nonneg_left hCube4
    (show 0 ≤ (12/κ)*(r:ℝ)*nAmbient by positivity)
  have hFork2 := mul_le_mul_of_nonneg_right (show (r:ℝ) ≤ r+1 from le_add_of_nonneg_right (by norm_num))
    (show 0 ≤ (12/κ)*(nAmbient:ℝ)*J^3 by positivity)
  have hFork : (roots:ℝ)*forkPaschPayment κ L nAmbient nHost ≤
      (12/κ)*(r+1)*nAmbient*J^3 := by
    nlinarith only [hFork0,hFork1,hFork2]
  have hRoute := route_payment_le_coefficient ha m L nAmbient w hw hAw
  change weightedCoreRoutePay a m nAmbient w (L+122) ≤
    ((nAmbient:ℝ)/w)*withdrawalRouteCoefficient a m*J^3 at hRoute
  have hR1R : (r1:ℝ) ≤ K*(r+1) := by exact_mod_cast hR1
  have hZR : (z:ℝ) ≤ nHost := Nat.cast_le.mpr hz
  have hPosRoute : 0 ≤ withdrawalRouteCoefficient a m := by unfold withdrawalRouteCoefficient; positivity
  have hRZ : ((r1*z:ℕ):ℝ) ≤ (K:ℝ)*(r+1)*nHost := by
    push_cast
    exact mul_le_mul hR1R hZR (Nat.cast_nonneg _) (by positivity)
  have hRoute1 := mul_le_mul_of_nonneg_left hRoute (Nat.cast_nonneg (r1*z))
  have hRoute2 := mul_le_mul_of_nonneg_right hRZ
    (show 0 ≤ ((nAmbient:ℝ)/w)*withdrawalRouteCoefficient a m*J^3 by positivity)
  have hRoute3 := mul_le_mul_of_nonneg_left hNw
    (show 0 ≤ (K:ℝ)*(r+1)*nAmbient*withdrawalRouteCoefficient a m*J^3 by positivity)
  have hRouting : ((r1*z:ℕ):ℝ)*weightedCoreRoutePay a m nAmbient w (L+122) ≤
      (4*(K:ℝ)/q*withdrawalRouteCoefficient a m)*(r+1)*nAmbient*J^3 := by
    have hEq : (K:ℝ)*(r+1)*nHost*(((nAmbient:ℝ)/w)*withdrawalRouteCoefficient a m*J^3)=
        ((nHost:ℝ)/w)*((K:ℝ)*(r+1)*nAmbient*withdrawalRouteCoefficient a m*J^3) := by ring
    rw [hEq] at hRoute2
    calc
      _ ≤ ((r1*z:ℕ):ℝ)*(((nAmbient:ℝ)/w)*withdrawalRouteCoefficient a m*J^3) := hRoute1
      _ ≤ ((nHost:ℝ)/w)*((K:ℝ)*(r+1)*nAmbient*withdrawalRouteCoefficient a m*J^3) := hRoute2
      _ = ((K:ℝ)*(r+1)*nAmbient*withdrawalRouteCoefficient a m*J^3)*((nHost:ℝ)/w) := by ring
      _ ≤ ((K:ℝ)*(r+1)*nAmbient*withdrawalRouteCoefficient a m*J^3)*(4/q) := hRoute3
      _ = _ := by ring
  have hQReal : (qSel:ℝ) ≤ (D:ℝ)*(K+1)*(r+1) := by exact_mod_cast hQ
  have hPayCoeff : ((61*r1+60*qSel:ℕ):ℝ) ≤ ((61*K+60*D*(K+1):ℕ):ℝ)*(r+1) := by
    push_cast
    nlinarith only [hR1R,hQReal]
  have hPay1 := mul_le_mul_of_nonneg_right hPayCoeff
    (show 0 ≤ 2*(nAmbient:ℝ)*((L+63:ℕ):ℝ)^3/κ by positivity)
  have hPay2 := mul_le_mul_of_nonneg_left hCube63
    (show 0 ≤ (2*((61*K+60*D*(K+1):ℕ):ℝ)/κ)*(r+1)*nAmbient by positivity)
  have hPayment : 2*((61*r1+60*qSel:ℕ):ℝ)*nAmbient*((L+63:ℕ):ℝ)^3/κ ≤
      (2*((61*K+60*D*(K+1):ℕ):ℝ)/κ)*(r+1)*nAmbient*J^3 := by
    calc
      _ = ((61*r1+60*qSel:ℕ):ℝ)*(2*(nAmbient:ℝ)*((L+63:ℕ):ℝ)^3/κ) := by ring
      _ ≤ ((61*K+60*D*(K+1):ℕ):ℝ)*(r+1)*(2*(nAmbient:ℝ)*((L+63:ℕ):ℝ)^3/κ) := hPay1
      _ = (2*((61*K+60*D*(K+1):ℕ):ℝ)/κ)*(r+1)*nAmbient*((L+63:ℕ):ℝ)^3 := by ring
      _ ≤ _ := hPay2
  unfold withdrawalRawPayment withdrawalGeometryCost
  change _ ≤ ((12/κ)+4*(K:ℝ)/q*withdrawalRouteCoefficient a m+
    2*((61*K+60*D*(K+1):ℕ):ℝ)/κ)*(r+1)*nAmbient*J^3
  calc
    _ ≤ (12/κ)*(r+1)*nAmbient*J^3+
        (4*(K:ℝ)/q*withdrawalRouteCoefficient a m)*(r+1)*nAmbient*J^3+
        (2*((61*K+60*D*(K+1):ℕ):ℝ)/κ)*(r+1)*nAmbient*J^3 :=
      add_le_add (add_le_add hFork hRouting) hPayment
    _ = _ := by ring

#print axioms withdrawalGeometryCost_pos
#print axioms withdrawal_raw_payment_le_uniform
end TypedTriangle.Pasch
