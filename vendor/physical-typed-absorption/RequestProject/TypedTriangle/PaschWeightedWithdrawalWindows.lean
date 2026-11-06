module
public import RequestProject.TypedTriangle.ExplicitResourceCore
public import RequestProject.TypedTriangle.PaschWeightedForkTupleCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V26 S07V27
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open CorePaid.Explicit

def weightedSelectorStockBudget (κ q a : ℝ) (m : ℕ) : ℝ :=
  min (selEps (Vortex.windowRouteRate a q m) (selA (m+1)))
    (paymentForbiddenBudget (κ/4) (q/4))
def weightedSelectorInputBudget (κ q a : ℝ) (m : ℕ) (τ : ℝ) : ℝ :=
  min (selEps (Vortex.windowRouteRate a q m) (selA (m+1)))
    (paymentInputBudget (κ/4) (q/4) τ (selA (m+1))
      (selQLimit (Vortex.windowRouteRate a q m) (selA (m+1))))
def weightedSelectorOrder (κ q a : ℝ) (m : ℕ) (τ : ℝ) : ℕ :=
  max (paymentOrder (κ/4) (q/4) τ (selA (m+1))
      (selQLimit (Vortex.windowRouteRate a q m) (selA (m+1))))
    (max ⌈200/min (Vortex.windowRouteRate a q m) 1⌉₊ ⌈16/(κ*q)⌉₊)
def weightedWithdrawalStockBudget (κ q a : ℝ) (m : ℕ) : ℝ :=
  min (forkEps κ) (weightedSelectorStockBudget κ q a m/4)
def weightedWithdrawalInputBudget (κ q a : ℝ) (m : ℕ) (τ : ℝ) : ℝ :=
  let K := forkQLimit κ+6
  min (forkEps κ)
    (min (min (weightedSelectorInputBudget κ q a m (τ/2)) (τ/2)/(4*K))
      (weightedSelectorStockBudget κ q a m/(8*K)))
def weightedWithdrawalOrder (κ q a : ℝ) (m : ℕ) (τ : ℝ) : ℕ :=
  max (max (weightedSelectorOrder κ q a m (τ/2)) ⌈32/κ⌉₊)
    ⌈1/weightedWithdrawalInputBudget κ q a m τ⌉₊

theorem weightedWithdrawal_budgets_pos {κ q a τ : ℝ} (m : ℕ)
    (hκ : 0 < κ) (hq : 0 < q) (ha : 0 < a) (hτ : 0 < τ) :
    0 < weightedWithdrawalStockBudget κ q a m ∧ 0 < weightedWithdrawalInputBudget κ q a m τ := by
  have hε := Vortex.windowRouteRate_pos m ha hq
  have hA : 0 < selA (m+1) := by unfold selA; omega
  have hθ : 0 < weightedSelectorStockBudget κ q a m :=
    lt_min (selEps_pos hε hA) (paymentForbiddenBudget_pos (by positivity) (by positivity))
  have hδ : 0 < weightedSelectorInputBudget κ q a m (τ/2) :=
    lt_min (selEps_pos hε hA) (paymentInputBudget_pos _ _ (by positivity) (by positivity) (by positivity))
  have hFork := forkEps_pos hκ
  constructor
  · exact lt_min (forkEps_pos hκ) (by positivity)
  · unfold weightedWithdrawalInputBudget; positivity

private theorem real_div_lt_nat_div_add_one (a p : ℕ) (hp : 0 < p) :
    (a:ℝ)/(p:ℝ) < (a/p:ℕ)+1 := by
  have hN : a < (a/p+1)*p := by
    have hm := Nat.mod_lt a hp
    have he := Nat.mod_add_div a p
    nlinarith only [hm,he]
  apply (div_lt_iff₀ (Nat.cast_pos.mpr hp)).mpr
  exact_mod_cast hN

/-- All scalar windows for the actual fork/selector constructor. The
forbidden cap precedes the requested output degree, and the real quotient
is paid from an extra quarter of the same geometric H3 pool. -/
theorem weighted_withdrawal_windows {κ q a τ : ℝ} (m : ℕ)
    (hκ : 0 < κ) (hq : 0 < q) (ha : 0 < a) (hτ : 0 < τ)
    (n N r b : ℕ) (hn : weightedWithdrawalOrder κ q a m τ ≤ n)
    (hN : q/4*n ≤ (N:ℝ))
    (hr : (r:ℝ) ≤ weightedWithdrawalInputBudget κ q a m τ*n)
    (hb : (b:ℝ) ≤ weightedWithdrawalStockBudget κ q a m*n) :
    let r1 := 3*r+forkQ κ r+4
    let b1 := b+3*r+forkQ κ r+4
    let A := selA (m+1)
    ∃ qSel p : ℕ, 0 < qSel ∧ qSel ≤ selQLimit (Vortex.windowRouteRate a q m) A*(r1+1) ∧ 0 < p ∧
      r1+b1+A*r1*n/qSel+(A+1)*r1+10*r1+m*(200*r1)  ≤  ⌊Vortex.windowRouteRate a q m*n⌋₊ ∧
      ((b1+61*r1+60*qSel+60:ℕ):ℝ) ≤ Vortex.windowRouteRate a q m*n ∧
      ((n*(61*r1+60*qSel):ℕ):ℝ)/(p:ℝ)+
        2*((max (A*r1) (60*r1+61*qSel)+r1+b1+3*(61*r1+60*qSel)+2*p:ℕ):ℝ) ≤ (κ/2)*N ∧
      ((2*r+forkQ κ r+4+max (A*r1) (60*r1+61*qSel)+2*(61*r1+60*qSel+p):ℕ):ℝ) ≤ τ*n ∧
      ((3*(61*r1+60*qSel)+2*p:ℕ):ℝ) ≤ τ*n := by
  intro r1 b1 A
  let ε := Vortex.windowRouteRate a q m
  have hε : 0 < ε := Vortex.windowRouteRate_pos m ha hq
  let D := selQLimit ε A
  let K := forkQLimit κ+6
  let θS := weightedSelectorStockBudget κ q a m
  let δS := weightedSelectorInputBudget κ q a m (τ/2)
  let u := min δS (τ/2)
  let δ := weightedWithdrawalInputBudget κ q a m τ
  let θ := weightedWithdrawalStockBudget κ q a m
  have hδ : 0 < δ := (weightedWithdrawal_budgets_pos m hκ hq ha hτ).2
  have hK : (1:ℝ) ≤ K := by dsimp [K]; exact_mod_cast (show 1 ≤ forkQLimit κ+6 by omega)
  have hnSel : weightedSelectorOrder κ q a m (τ/2) ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnδ : ⌈1/δ⌉₊ ≤ n := (le_max_right _ _).trans hn
  have hδn : 1 ≤ δ*n := by
    have hc : (⌈1/δ⌉₊:ℝ) ≤ n := Nat.cast_le.mpr hnδ
    have hh := (Nat.le_ceil (1/δ)).trans hc
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hh
  have hQ := (forkQ_limit_spec hκ).2 r
  have hSize : r1 ≤ K*(r+1) := by dsimp [r1,K]; nlinarith only [hQ]
  have hδK : 2*(K:ℝ)*δ ≤ u := by
    have hh : δ ≤ u/(4*K) := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ (by positivity : (0:ℝ) < 4*K)).mp hh
    have hProd : 0 ≤ (K:ℝ)*δ := mul_nonneg (by positivity) hδ.le
    nlinarith only [hh',hProd]
  have hδStock : 2*(K:ℝ)*δ ≤ θS/4 := by
    have hh : δ ≤ θS/(8*K) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by positivity : (0:ℝ) < 8*K)).mp hh
    linarith only [hh']
  have hN0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hR1 : (r1:ℝ) ≤ u*n := by
    have hs : (r1:ℝ) ≤ K*(r+1) := by exact_mod_cast hSize
    have ht := mul_le_mul_of_nonneg_left (show (r:ℝ)+1 ≤ 2*δ*n by linarith only [hr,hδn]) (show (0:ℝ) ≤ K by positivity)
    have hh := mul_le_mul_of_nonneg_right hδK hN0
    push_cast at hs
    nlinarith only [hs,ht,hh]
  have hB1 : (b1:ℝ) ≤ θS*n := by
    have hs : (r1:ℝ) ≤ K*(r+1) := by exact_mod_cast hSize
    have ht := mul_le_mul_of_nonneg_left (show (r:ℝ)+1 ≤ 2*δ*n by linarith only [hr,hδn]) (show (0:ℝ) ≤ K by positivity)
    have hh := mul_le_mul_of_nonneg_right hδStock hN0
    have hθn := mul_le_mul_of_nonneg_right (show θ ≤ θS/4 from min_le_right _ _) hN0
    have he : b1=b+r1 := by dsimp [b1,r1]; ring
    rw [he,Nat.cast_add]
    push_cast at hs
    nlinarith only [hs,ht,hh,hθn,hb]
  have hrS : (r1:ℝ) ≤ selEps ε A*n :=
    (hR1.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hN0)).trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hN0)
  have hbS : (b1:ℝ) ≤ selEps ε A*n := hB1.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hN0)
  have hn200 : 200 ≤ min ε 1*n := by
    have hc : ⌈200/min ε 1⌉₊ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hnSel)
    have hh := (Nat.le_ceil (200/min ε 1)).trans (Nat.cast_le.mpr hc)
    simpa only [mul_comm] using (div_le_iff₀ (lt_min hε one_pos)).mp hh
  obtain ⟨hBud,hRho⟩ := selector_window hε (t:=m+1) (A:=A) (by dsimp [A]; exact le_rfl) hrS hbS hn200
  let qSel := selQ ε A r1
  have hQSel := (selQ_limit_spec hε A).2 r1
  have hrPay : (r1:ℝ) ≤ paymentInputBudget (κ/4) (q/4) (τ/2) A D*n :=
    (hR1.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hN0)).trans
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hN0)
  have hbPay : (b1:ℝ) ≤ paymentForbiddenBudget (κ/4) (q/4)*n :=
    hB1.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hN0)
  obtain ⟨p,hp,hWin,hFuel,hRes⟩ := payment_window_explicit (κ/4) (q/4)
    (by positivity) (by positivity) A D (τ/2) (by positivity) n N r1 b1 qSel
    ((le_max_left _ _).trans hnSel) hN hQSel hrPay hbPay
  have hNlarge : 1 ≤ (κ/4)*N := by
    have hc : ⌈16/(κ*q)⌉₊ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hnSel)
    have ht := (div_le_iff₀ (mul_pos hκ hq)).mp ((Nat.le_ceil (16/(κ*q))).trans (Nat.cast_le.mpr hc))
    have hs := mul_le_mul_of_nonneg_left hN hκ.le
    nlinarith only [ht,hs]
  have hQuot := real_div_lt_nat_div_add_one (n*(61*r1+60*qSel)) p hp
  have hWinReal : ((n*(61*r1+60*qSel):ℕ):ℝ)/(p:ℝ)+
      2*((max (A*r1) (60*r1+61*qSel)+r1+b1+3*(61*r1+60*qSel)+2*p:ℕ):ℝ) ≤ (κ/2)*N := by
    push_cast at hWin hQuot ⊢
    linarith only [hQuot,hWin,hNlarge]
  have hForkSmall : ((2*r+forkQ κ r+4:ℕ):ℝ) ≤ (τ/2)*n := by
    have hs : (2*r+forkQ κ r+4:ℕ) ≤ r1 := by dsimp [r1]; omega
    exact (Nat.cast_le.mpr hs).trans (hR1.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hN0))
  refine ⟨qSel,p,selQ_pos ε A r1,hQSel,hp,?_,hRho,hWinReal,?_,?_⟩
  · simpa only [Nat.add_sub_cancel] using hBud
  · have hh := hFuel
    push_cast at hh hForkSmall ⊢
    linarith only [hh,hForkSmall]
  · exact hRes.trans (mul_le_mul_of_nonneg_right (show τ/2 ≤ τ by linarith only [hτ]) hN0)

#print axioms weightedWithdrawal_budgets_pos
#print axioms weighted_withdrawal_windows
end TypedTriangle.Pasch
