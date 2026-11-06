/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4NativeScaleCapPackage
public import RequestProject.TypedTriangle.G3UniformPayment
public import RequestProject.TypedTriangle.CoreForkOnPool
public import RequestProject.TypedTriangle.VortexWithdrawalCoreIncidence
public import RequestProject.TypedTriangle.ExplicitBankCore
public import RequestProject.TypedTriangle.VortexFixedWindowStructuredResources
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Numerical resource component: ExplicitBankScaleCap. -/
namespace TypedTriangle.StockEntry.Explicit

def bankGamma (q ε : ℝ) : ℝ := ε*q/8
def bankEta (κ q ε : ℝ) (B : ℕ) : ℝ := min (κ*q^2/8) (bankGamma q ε/((B:ℝ)+1))
def smallMomentCap (L η : ℝ) : ℝ := η/(2+15*L)
def monitorCap (L η : ℝ) (K : ℕ) : ℝ := smallMomentCap L (η/((K:ℝ)+1))
def bankOrder (κ q : ℝ) : ℕ := ⌈8/(κ*q^2)⌉₊+1

theorem native_bank_scales_explicit (κ q ε : ℝ) (B : ℕ)
    (hκ : 0 < κ) (hq : 0 < q) (hε : 0 < ε) :
    let γ := bankGamma q ε
    let η := bankEta κ q ε B
    0 < γ ∧ 0 < η ∧ η ≤ κ * q ^ 2 / 8 ∧
      η * B / γ ≤ 1 ∧
      ∀ n w qSel : ℕ, q * n / 2 ≤ w →
        ε * w / 4 ≤ qSel → γ * n ≤ qSel := by
  let γ := bankGamma q ε
  have hγ : 0 < γ := by dsimp [γ,bankGamma]; positivity
  let η := bankEta κ q ε B
  have hη : 0 < η := by dsimp [η,bankEta,bankGamma]; positivity
  dsimp only
  refine ⟨hγ, hη, min_le_left _ _, ?_, ?_⟩
  · have hη' : η ≤ γ / ((B : ℝ) + 1) := min_le_right _ _
    have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    have hD : (0 : ℝ) < B + 1 := by positivity
    have hprod := mul_le_mul_of_nonneg_right hη' hB
    apply (div_le_iff₀ hγ).2
    have hquot : γ / ((B : ℝ) + 1) * B ≤ γ := by
      calc
        γ / ((B : ℝ) + 1) * B = γ * B / ((B : ℝ) + 1) := by ring
        _ ≤ γ := (div_le_iff₀ hD).2 (by nlinarith only [hγ, hB])
    nlinarith only [hprod, hquot]
  · intro n w qSel hw hsel
    dsimp [γ,bankGamma]
    have hw' := mul_le_mul_of_nonneg_left hw (show 0 ≤ ε / 4 by positivity)
    nlinarith only [hw', hsel]

theorem small_positive_moment_cap_explicit (L η : ℝ) (hL : 0 ≤ L) (hη : 0 < η) :
    0 < smallMomentCap L η ∧
      ∀ τ ηPack ρ τSel : ℝ,
        τ ≤ smallMomentCap L η → ηPack ≤ smallMomentCap L η →
        ρ ≤ smallMomentCap L η → τSel ≤ smallMomentCap L η →
        τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel) ≤ η := by
  refine ⟨by unfold smallMomentCap; positivity, ?_⟩
  change ∀ τ ηPack ρ τSel : ℝ, τ ≤ η/(2+15*L) → ηPack ≤ η/(2+15*L) →
    ρ ≤ η/(2+15*L) → τSel ≤ η/(2+15*L) → _
  intro τ ηPack ρ τSel hτ hPack hρ hSel
  have hsum : ηPack + 2 * ρ + 2 * τSel ≤ 5 * (η / (2 + 15 * L)) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 3 * L / 2 by positivity)
  have hden : 0 < 2 + 15 * L := by positivity
  have hscale : (η / (2 + 15 * L)) * (2 + 15 * L) = η := by
    field_simp
  nlinarith only [hmul, hτ, hscale, hη.le]

theorem uniform_monitor_moment_cap_explicit (L η : ℝ) (K : ℕ)
    (hL : 0 ≤ L) (hη : 0 < η) :
    0 < monitorCap L η K ∧
      ∀ τ ηPack ρ τSel : ℝ,
        τ ≤ monitorCap L η K → ηPack ≤ monitorCap L η K →
        ρ ≤ monitorCap L η K → τSel ≤ monitorCap L η K →
        (K : ℝ) *
          (τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel)) ≤ η := by
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hηK : 0 < η / ((K : ℝ) + 1) := div_pos hη hKpos
  obtain ⟨hδ,hcap⟩ := small_positive_moment_cap_explicit L (η / ((K : ℝ)+1)) hL hηK
  refine ⟨hδ, ?_⟩
  intro τ ηPack ρ τSel hτ hPack hρ hSel
  have hbudget := hcap τ ηPack ρ τSel hτ hPack hρ hSel
  have hK : (K : ℝ) ≤ (K : ℝ) + 1 := by linarith
  have hquot : ((K : ℝ) + 1) * (η / ((K : ℝ) + 1)) = η := by field_simp
  by_cases hnonneg : 0 ≤ τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel)
  · calc
      (K : ℝ) * (τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel))
          ≤ ((K : ℝ) + 1) * (τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel)) :=
            mul_le_mul_of_nonneg_right hK hnonneg
      _ ≤ ((K : ℝ) + 1) * (η / ((K : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hbudget hKpos.le
      _ = η := hquot
  · have hneg : τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel) < 0 :=
      lt_of_not_ge hnonneg
    have hk0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    exact (mul_nonpos_of_nonneg_of_nonpos hk0 hneg.le).trans hη.le


theorem bank_order_explicit (κ q : ℝ) (hκ : 0 < κ) (hq : 0 < q) :
    ∀ n : ℕ, bankOrder κ q ≤ n →
      8 ≤ κ * q ^ 2 * (n : ℝ) ^ 2 := by
  let a := κ * q ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  intro n hn
  change ⌈8/a⌉₊+1 ≤ n at hn
  have hnOne : 1 ≤ n := by omega
  have hbound : 8 / a ≤ (n : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_trans
      (Nat.le_add_right _ _) hn))
  have hlinear : 8 ≤ a * (n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ ha).mp hbound
  have hquad : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hnOne
    nlinarith
  have hgrow := mul_le_mul_of_nonneg_left hquad ha.le
  dsimp [a] at hlinear hgrow
  nlinarith only [hlinear, hgrow]


/-- Literal parameters for the quadratic bank and all monitor coordinates. -/
theorem native_bank_scale_cap_explicit (κ q ε Λ : ℝ) (B K : ℕ)
    (hκ : 0 < κ) (hq : 0 < q) (hε : 0 < ε) (hΛ : 0 ≤ Λ) :
    let γ := bankGamma q ε
    let η := bankEta κ q ε B
    let δ := monitorCap Λ η K
    0 < γ ∧ 0 < η ∧ 0 < δ ∧ η ≤ κ*q^2/8 ∧ η*B/γ ≤ 1 ∧
      (∀ n w qSel : ℕ,q*n/2 ≤ w → ε*w/4 ≤ qSel → γ*n ≤ qSel) ∧
      (∀ τ ηPack ρ τSel : ℝ,τ ≤ δ → ηPack ≤ δ → ρ ≤ δ → τSel ≤ δ →
        (K:ℝ)*(τ+(3*Λ/2)*(ηPack+2*ρ+2*τSel)) ≤ η) ∧
      ∀ n : ℕ,bankOrder κ q ≤ n → 8 ≤ κ*q^2*(n:ℝ)^2 := by
  dsimp only
  obtain ⟨hγ,hη,hηκ,hCapacity,hqn⟩ := native_bank_scales_explicit κ q ε B hκ hq hε
  obtain ⟨hδ,hKB⟩ := uniform_monitor_moment_cap_explicit Λ (bankEta κ q ε B) K hΛ hη
  exact ⟨hγ,hη,hδ,hηκ,hCapacity,hqn,hKB,bank_order_explicit κ q hκ hq⟩

#print axioms native_bank_scales_explicit
#print axioms small_positive_moment_cap_explicit
#print axioms uniform_monitor_moment_cap_explicit
#print axioms bank_order_explicit
#print axioms native_bank_scale_cap_explicit
end TypedTriangle.StockEntry.Explicit

/-! Numerical resource component: ExplicitUniformPayment. -/
namespace TypedTriangle.CorePaid.Explicit
open S07V26

def selQLimit (ε : ℝ) (A : ℕ) : ℕ := ⌈4*(A:ℝ)/min ε 1⌉₊+2
def forkQLimit (κ : ℝ) : ℕ := ⌈128/κ⌉₊+1
def paymentForbiddenBudget (κ μ : ℝ) : ℝ := κ*μ/16
def paymentT (A D : ℕ) : ℕ := A+61*D+61
def paymentGamma (κ μ τ : ℝ) : ℝ := min (κ*μ/32) (τ/8)
def paymentJ (κ μ τ : ℝ) : ℕ := ⌈1/paymentGamma κ μ τ⌉₊
def paymentCost (κ μ τ : ℝ) (A D : ℕ) : ℝ :=
  2*((paymentJ κ μ τ:ℝ)+8)*paymentT A D+4
def paymentInputBudget (κ μ τ : ℝ) (A D : ℕ) : ℝ :=
  min (κ*μ/(8*paymentCost κ μ τ A D)) (τ/(12*paymentT A D))
def paymentOrder (κ μ τ : ℝ) (A D : ℕ) : ℕ :=
  max (max ⌈1/paymentInputBudget κ μ τ A D⌉₊ ⌈1/paymentGamma κ μ τ⌉₊) 1

theorem paymentForbiddenBudget_pos {κ μ : ℝ} (hκ : 0 < κ) (hμ : 0 < μ) :
    0 < paymentForbiddenBudget κ μ := by unfold paymentForbiddenBudget; positivity

theorem paymentInputBudget_pos {κ μ τ : ℝ} (A D : ℕ)
    (hκ : 0 < κ) (hμ : 0 < μ) (hτ : 0 < τ) : 0 < paymentInputBudget κ μ τ A D := by
  unfold paymentInputBudget paymentCost paymentT
  positivity

theorem selQ_limit_spec {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    1 ≤ selQLimit ε A ∧ ∀ r, S07V27.selQ ε A r ≤ selQLimit ε A*(r+1) := by
  let c : ℝ := 4*(A:ℝ)/min ε 1
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let D := selQLimit ε A
  refine ⟨by unfold selQLimit; omega,?_⟩
  intro r
  have hcD : c+2 ≤ (D:ℝ) := by
    dsimp [D,selQLimit]; push_cast; linarith [Nat.le_ceil c]
  have hq : (S07V27.selQ ε A r:ℝ) ≤ c*r+2 := by
    unfold S07V27.selQ
    push_cast
    have hnon : 0 ≤ 4*(A:ℝ)*r/min ε 1 := by positivity
    have hh := Nat.ceil_lt_add_one hnon
    have heq : 4*(A:ℝ)*r/min ε 1 = c*r := by dsimp [c]; ring
    linarith
  have hR : (S07V27.selQ ε A r:ℝ) ≤ D*(r+1) := by
    have := mul_le_mul_of_nonneg_right hcD (show (0:ℝ) ≤ r by positivity)
    nlinarith
  exact_mod_cast hR

theorem forkQ_limit_spec {κ : ℝ} (hκ : 0 < κ) :
    1 ≤ forkQLimit κ ∧ ∀ r, forkQ κ r ≤ forkQLimit κ*(r+1) := by
  let D := forkQLimit κ
  refine ⟨by unfold forkQLimit; omega,?_⟩
  intro r
  have h1 := forkQ_upper hκ r
  have heq : 128*(r:ℝ)/κ = (128/κ)*r := by ring
  rw [heq] at h1
  have h2 : 128/κ+1 ≤ (D:ℝ) := by dsimp [D,forkQLimit]; push_cast; linarith [Nat.le_ceil (128/κ)]
  have h3 := mul_le_mul_of_nonneg_right h2 (show (0:ℝ) ≤ r by positivity)
  have h4 : 0 ≤ 128/κ := by positivity
  have h5 : (forkQ κ r:ℝ) ≤ D*(r+1) := by nlinarith
  exact_mod_cast h5

theorem payment_window_explicit (κ μ : ℝ) (hκ : 0 < κ) (hμ : 0 < μ)
    (A D : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    let θ := paymentForbiddenBudget κ μ
    let δ := paymentInputBudget κ μ τ A D
    ∀ n N r b q : ℕ, paymentOrder κ μ τ A D ≤ n → μ*n ≤ N → q ≤ D*(r+1) →
        (r:ℝ) ≤ δ*n → (b:ℝ) ≤ θ*n →
        ∃ p : ℕ, 0 < p ∧
          ((n*(61*r+60*q)/p +
            2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) < κ*N ∧
          ((max (A*r) (60*r+61*q)+2*(61*r+60*q+p):ℕ):ℝ) ≤ τ*n ∧
          ((3*(61*r+60*q)+2*p:ℕ):ℝ) ≤ τ*n := by
  dsimp only
  let θ := paymentForbiddenBudget κ μ
  let T := paymentT A D
  have hT : (0:ℝ) < T := by dsimp [T,paymentT]; positivity
  let γ := paymentGamma κ μ τ
  have hγ : 0 < γ := lt_min (by positivity) (by positivity)
  let J := paymentJ κ μ τ
  have hJ : 1 ≤ (J:ℝ)*γ := by
    have := Nat.le_ceil (1/γ)
    exact (div_le_iff₀ hγ).mp this
  let C := paymentCost κ μ τ A D
  have hC : 0 < C := by dsimp [C,paymentCost]; positivity
  let δ := paymentInputBudget κ μ τ A D
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  intro n N r b q hn hN hq hr hb
  change max (max ⌈1/δ⌉₊ ⌈1/γ⌉₊) 1 ≤ n at hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hδn : 1 ≤ δ*n := by
    have hh : (⌈1/δ⌉₊:ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans ((le_max_left _ _).trans hn)
    have := (Nat.le_ceil (1/δ)).trans hh
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp this
  have hγn : 1 ≤ γ*n := by
    have hh : (⌈1/γ⌉₊:ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans ((le_max_left _ _).trans hn)
    have := (Nat.le_ceil (1/γ)).trans hh
    simpa only [mul_comm] using (div_le_iff₀ hγ).mp this
  let p : ℕ := ⌈γ*n⌉₊
  have hpR : γ*n ≤ (p:ℝ) := Nat.le_ceil _
  have hp : 0 < p := by exact_mod_cast (show (0:ℝ) < p by linarith)
  have hpHi : (p:ℝ) ≤ 2*γ*n := by
    have := Nat.ceil_lt_add_one (show 0 ≤ γ*n by positivity)
    change (⌈γ*n⌉₊:ℝ) ≤ _
    linarith
  have hnJ : n ≤ J*p := by
    have h1 := mul_le_mul_of_nonneg_right hJ hnpos.le
    have h2 := mul_le_mul_of_nonneg_left hpR (show (0:ℝ) ≤ J by positivity)
    exact_mod_cast (show (n:ℝ) ≤ J*p by nlinarith)
  have hy : 61*r+60*q ≤ T*(r+1) := by dsimp [T,paymentT]; nlinarith
  have hz : max (A*r) (60*r+61*q) ≤ T*(r+1) := by
    apply max_le
    · dsimp [T,paymentT]; nlinarith
    · dsimp [T,paymentT]; nlinarith
  have hdiv : n*(61*r+60*q)/p ≤ J*(61*r+60*q) := by
    apply (Nat.div_le_iff_le_mul hp).mpr
    calc n*(61*r+60*q) ≤ (J*p)*(61*r+60*q) := Nat.mul_le_mul_right _ hnJ
      _ ≤ J*(61*r+60*q)*p+p-1 := by
        have heq : (J*p)*(61*r+60*q) = J*(61*r+60*q)*p := by ring
        rw [heq]
        omega
  have hcost : n*(61*r+60*q)/p +
      2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p) ≤
      (J+8)*T*(r+1)+2*r+2*b+4*p := by nlinarith
  have hcostR : ((n*(61*r+60*q)/p +
      2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) ≤
      C*δ*n+2*b+8*γ*n := by
    have hcR : ((n*(61*r+60*q)/p +
        2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) ≤
        (J+8)*T*(r+1)+2*r+2*b+4*p := by exact_mod_cast hcost
    have hscaled := mul_le_mul_of_nonneg_left (show (r:ℝ)+1 ≤ 2*δ*n by linarith)
      (show (0:ℝ) ≤ (J+8)*T by positivity)
    dsimp [C,paymentCost]
    nlinarith
  have hδC : C*δ ≤ κ*μ/8 := by
    have h := min_le_left (κ*μ/(8*C)) (τ/(12*T))
    change δ ≤ _ at h
    have := (le_div_iff₀ (show 0 < 8*C by positivity)).mp h
    linarith
  have hγK : 8*γ ≤ κ*μ/4 := by
    have := min_le_left (κ*μ/32) (τ/8)
    change γ ≤ _ at this
    linarith
  have hθK : 2*θ ≤ κ*μ/8 := by dsimp [θ,paymentForbiddenBudget]; linarith [mul_nonneg hκ.le hμ.le]
  have hδT : 6*T*δ ≤ τ/2 := by
    have h := min_le_right (κ*μ/(8*C)) (τ/(12*T))
    change δ ≤ _ at h
    have := (le_div_iff₀ (show (0:ℝ) < 12*T by positivity)).mp h
    linarith
  have hγT : 4*γ ≤ τ/2 := by
    have := min_le_right (κ*μ/32) (τ/8)
    change γ ≤ _ at this
    linarith
  have hsmall : 6*T*δ*n+4*γ*n ≤ τ*n := by
    have := mul_le_mul_of_nonneg_right hδT hnpos.le
    have := mul_le_mul_of_nonneg_right hγT hnpos.le
    nlinarith
  have hyR : ((61*r+60*q:ℕ):ℝ) ≤ T*(r+1) := by exact_mod_cast hy
  have hzR : ((max (A*r) (60*r+61*q):ℕ):ℝ) ≤ T*(r+1) := by exact_mod_cast hz
  have hsc := mul_le_mul_of_nonneg_left (show (r:ℝ)+1 ≤ 2*δ*n by linarith) hT.le
  refine ⟨p,hp,?_,?_,?_⟩
  · have h1 := mul_le_mul_of_nonneg_right hδC hnpos.le
    have h2 := mul_le_mul_of_nonneg_right hγK hnpos.le
    have h5 := mul_le_mul_of_nonneg_right hθK hnpos.le
    have h3 := mul_le_mul_of_nonneg_left hN hκ.le
    have h4 : 0 < κ*μ*n := by positivity
    nlinarith only [hcostR,h1,h2,h5,hb,h3,h4]
  · push_cast at hyR hzR ⊢
    nlinarith
  · push_cast at hyR hzR ⊢
    nlinarith




#print axioms selQ_limit_spec
#print axioms forkQ_limit_spec
#print axioms payment_window_explicit
end TypedTriangle.CorePaid.Explicit

/-! Numerical resource component: ExplicitUniformWithdrawal. -/
namespace TypedTriangle.CorePaid.Explicit
open CorePayment PreparedSupply SelSimul SelBridge SelTyped S07V26

def selectorStockBudget (α q ε : ℝ) (t : ℕ) : ℝ :=
  min (S07V27.selEps ε (S07V27.selA t)) (paymentForbiddenBudget (q*α/2) (q/2))
def selectorInputBudget (α q ε : ℝ) (t : ℕ) (τ : ℝ) : ℝ :=
  min (S07V27.selEps ε (S07V27.selA t))
    (paymentInputBudget (q*α/2) (q/2) τ (S07V27.selA t) (selQLimit ε (S07V27.selA t)))
def selectorOrder (α q ε : ℝ) (t : ℕ) (τ : ℝ) : ℕ :=
  max (paymentOrder (q*α/2) (q/2) τ (S07V27.selA t) (selQLimit ε (S07V27.selA t)))
    ⌈200/min ε 1⌉₊
def withdrawalStockBudget (α q ε : ℝ) (t : ℕ) : ℝ :=
  min (forkEps (q*α/2)) (selectorStockBudget α q ε t/4)
def withdrawalInputBudget (α q ε : ℝ) (t : ℕ) (τ : ℝ) : ℝ :=
  let κ := q*α/2
  let K := forkQLimit κ+6
  let u := min (selectorInputBudget α q ε t (τ/2)) (τ/2)
  min (forkEps κ) (min (u/(4*K)) (selectorStockBudget α q ε t/(8*K)))
def withdrawalOrder (α q ε : ℝ) (t : ℕ) (τ : ℝ) : ℕ :=
  max (max (selectorOrder α q ε t (τ/2)) ⌈32/(q*α/2)⌉₊)
    ⌈1/withdrawalInputBudget α q ε t τ⌉₊

theorem selectorStockBudget_pos {α q ε : ℝ} (t : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hε : 0 < ε) : 0 < selectorStockBudget α q ε t :=
  lt_min (S07V27.selEps_pos hε (by unfold S07V27.selA; omega))
    (paymentForbiddenBudget_pos (by positivity) (by positivity))
theorem selectorInputBudget_pos {α q ε τ : ℝ} (t : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hε : 0 < ε) (hτ : 0 < τ) :
    0 < selectorInputBudget α q ε t τ :=
  lt_min (S07V27.selEps_pos hε (by unfold S07V27.selA; omega))
    (paymentInputBudget_pos _ _ (by positivity) (by positivity) hτ)
theorem withdrawalStockBudget_pos {α q ε : ℝ} (t : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hε : 0 < ε) : 0 < withdrawalStockBudget α q ε t :=
  lt_min (forkEps_pos (by positivity)) (div_pos (selectorStockBudget_pos t hα hq hε) (by norm_num))
theorem withdrawalInputBudget_pos {α q ε τ : ℝ} (t : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hε : 0 < ε) (hτ : 0 < τ) :
    0 < withdrawalInputBudget α q ε t τ := by
  have hFork := forkEps_pos (show 0 < q*α/2 by positivity)
  have hS := selectorStockBudget_pos t hα hq hε
  have hδ := selectorInputBudget_pos t hα hq hε (half_pos hτ)
  unfold withdrawalInputBudget
  positivity

theorem fixed_core_paid_selector_layer_explicit_with_core_incidence (α q0 ε : ℝ) (t : ℕ)
    (hα : 0 < α) (hq0 : 0 < q0)
    (ht : Odd t) (ht3 : 3 ≤ t) (hε : 0 < ε) :
    ∀ τ : ℝ, 0 < τ →
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        IsPhysical H F (edges H) → selectorOrder α q0 ε t τ ≤ Fintype.card V →
        q0*Fintype.card V/2 ≤ W.card →
        (∀ u v : V, u ≠ v → ∀ k : I, ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
          q0*α*Fintype.card V/2 ≤ ((commonNbrs H k u v) ∩ W).card) →
        S07V27.RouteProp H.G H.lab F t ε W →
          ∀ (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj]
            (r b : ℕ), X ≤ H.G →
            (∀ x y, X.Adj x y → x ∈ W ∨ y ∈ W) →
            (∀ v, X.degree v ≤ r) → (∀ v, B0.degree v ≤ b) →
            (r:ℝ) ≤ selectorInputBudget α q0 ε t τ*Fintype.card V → (b:ℝ) ≤ selectorStockBudget α q0 ε t*Fintype.card V →
            ∃ (σ : V → LocalSel V) (C : Finset (Sym2 V)),
              Disjoint (fuelU (univ \ W) σ ∪ C) (X.edgeFinset ∪ B0.edgeFinset) ∧
              Basal H F (fuelU (univ \ W) σ ∪ C) ∧
              Basal H F (SelSimul.residual X (univ \ W) σ ∅ ∪ C) ∧
              (∀ e ∈ fuelU (univ \ W) σ ∪ C, ∃ v ∈ e, v ∈ W) ∧
              (∀ v, (edeg (fuelU (univ \ W) σ ∪ C) v:ℝ) ≤ τ*Fintype.card V) ∧
              ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → IsPhysical H F L →
                (fuelU (univ \ W) σ ∪ C) ∪ L =
                  packEdges (packing X (univ \ W) σ L) ∪ (SelSimul.residual X (univ \ W) σ L ∪ C) ∧
                Disjoint (packEdges (packing X (univ \ W) σ L)) (SelSimul.residual X (univ \ W) σ L ∪ C) ∧
                Basal H F (packEdges (packing X (univ \ W) σ L)) ∧
                (∀ e ∈ SelSimul.residual X (univ \ W) σ L ∪ C, ∀ v ∈ e, v ∈ W) ∧
                (∀ v, (edeg (SelSimul.residual X (univ \ W) σ L ∪ C) v:ℝ) ≤ τ*Fintype.card V) ∧
                IsPhysical H F (SelSimul.residual X (univ \ W) σ L ∪ C) := by
  let A := S07V27.selA t
  have hA : 0 < A := by dsimp [A,S07V27.selA]; omega
  let D := selQLimit ε A
  obtain ⟨hD,hqBound⟩ := selQ_limit_spec hε A
  let κ := q0*α/2
  let μ := q0/2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hμ : 0 < μ := by dsimp [μ]; positivity
  let θP := paymentForbiddenBudget κ μ
  let θ := selectorStockBudget α q0 ε t
  intro τ hτ
  let δP := paymentInputBudget κ μ τ A D
  let nPay := paymentOrder κ μ τ A D
  have hPay := payment_window_explicit κ μ hκ hμ A D τ hτ
  let δ := selectorInputBudget α q0 ε t τ
  intro V I _ H F W h2 hn hWlow hpool' hroute
  change max nPay ⌈200/min ε 1⌉₊ ≤ Fintype.card V at hn
  intro X B0 _ _ r b hXG hXW hX hB hr hb
  have hlow : μ*Fintype.card V ≤ Fintype.card (Survivors (univ \ W)) := by
    rw [card_survivors_compl]
    dsimp [μ]
    nlinarith [hWlow]
  have hcore : CommonNbrCond (restrictedHost H (univ \ W)) F κ :=
    commonNbrCond_of_core_pool H F W hκ.le (by
      intro u v hne k hk
      have hp := hpool' u v hne k hk
      change κ*Fintype.card V ≤ _
      dsimp [κ]
      nlinarith [hp])
  have hrP : (r:ℝ) ≤ δP*Fintype.card V := hr.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  have hbP : (b:ℝ) ≤ θP*Fintype.card V := hb.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  obtain ⟨p,hp,hpWindow,hFuel,hRes⟩ := hPay (Fintype.card V)
    (Fintype.card (Survivors (univ \ W))) r b (S07V27.selQ ε A r)
    ((le_max_left _ _).trans hn) hlow (hqBound r) hrP hbP
  have hrS : (r:ℝ) ≤ S07V27.selEps ε A*Fintype.card V := hr.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hbS : (b:ℝ) ≤ S07V27.selEps ε A*Fintype.card V := hb.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have he : 0 < min ε 1 := lt_min hε one_pos
  have hn200 : 200 ≤ min ε 1*Fintype.card V := by
    have hc : (⌈200/min ε 1⌉₊:ℝ) ≤ Fintype.card V := by
      exact_mod_cast (le_max_right _ _).trans hn
    have hh := (Nat.le_ceil (200/min ε 1)).trans hc
    simpa only [mul_comm] using (div_le_iff₀ he).mp hh
  obtain ⟨hBud,hρ⟩ := S07V27.selector_window hε (t := t) (A := A)
    (by dsimp [A,S07V27.selA]; omega) hrS hbS hn200
  obtain ⟨hZW,hZ⟩ := S07V27.allRoots_hyps W X hXW
  obtain ⟨σ,C,hAvoid,hBas,hEmpty,hInc,hDeg,hModes⟩ := selector_paid_layer_host_with_core_incidence ht ht3 hε
    hroute X B0 (univ \ W) hZ hZW hXG h2 hcore
    (by dsimp [A,S07V27.selA]; omega) (S07V27.selQ_pos ε A r) hp hX hB hBud hρ hpWindow
  refine ⟨σ,C,hAvoid,hBas,hEmpty,?_,?_,?_⟩
  · intro e he
    obtain ⟨v,hv,hvZ⟩ := hInc e he
    exact ⟨v,hv,by simpa using hvZ⟩
  · intro v
    exact (show (edeg (fuelU (univ \ W) σ ∪ C) v:ℝ) ≤
      ((max (A*r) (60*r+61*S07V27.selQ ε A r)+2*(61*r+60*S07V27.selQ ε A r+p):ℕ):ℝ) by
        exact_mod_cast hDeg v).trans hFuel
  · intro L hL hphys
    obtain ⟨heq,hd,hB,hW,hD,hPhys⟩ := hModes L hL hphys
    refine ⟨heq,hd,hB,?_,?_,hPhys⟩
    · intro e he v hv
      have := hW e he v hv
      simpa using this
    · intro v
      exact (show (edeg (SelSimul.residual X (univ \ W) σ L ∪ C) v:ℝ) ≤
        ((3*(61*r+60*S07V27.selQ ε A r)+2*p:ℕ):ℝ) by exact_mod_cast hD v).trans hRes




theorem fixed_core_positive_withdrawal_explicit_with_core_incidence (α q0 ε : ℝ) (t : ℕ)
    (hα : 0 < α) (hq0 : 0 < q0)
    (ht : Odd t) (ht3 : 3 ≤ t) (hε : 0 < ε) :
    ∀ τ : ℝ, 0 < τ →
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        IsPhysical H F (edges H) → withdrawalOrder α q0 ε t τ ≤ Fintype.card V →
        q0*Fintype.card V/2 ≤ W.card →
        (∀ u v : V, u ≠ v → ∀ k : I, ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
          q0*α*Fintype.card V/2 ≤ ((commonNbrs H k u v) ∩ W).card) →
        S07V27.RouteProp H.G H.lab F t ε W →
          ∀ (X B : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B.Adj]
            (r b : ℕ), X ≤ H.G →
            (∀ v, X.degree v ≤ r) → (∀ v, B.degree v ≤ b) →
            (r:ℝ) ≤ withdrawalInputBudget α q0 ε t τ*Fintype.card V → (b:ℝ) ≤ withdrawalStockBudget α q0 ε t*Fintype.card V →
            ∃ R : Finset (Sym2 V), Disjoint R (X.edgeFinset ∪ B.edgeFinset) ∧
              Basal H F R ∧ (∀ e ∈ R, ∃ v ∈ e, v ∈ W) ∧ (∀ v, (edeg R v:ℝ) ≤ τ*Fintype.card V) ∧
              (∃ Y0 : Finset (Sym2 V), Basal H F Y0 ∧ Y0 ⊆ R ∧
                (∀ e ∈ Y0, ∀ v ∈ e, v ∈ W) ∧
                (∀ v, (edeg Y0 v:ℝ) ≤ τ*Fintype.card V)) ∧
              ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → IsPhysical H F L →
                ∃ P Y : Finset (Sym2 V),
                  R ∪ L = P ∪ Y ∧ Disjoint P Y ∧ Basal H F P ∧
                  (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
                  (∀ v, (edeg Y v:ℝ) ≤ τ*Fintype.card V) ∧ IsPhysical H F Y := by
  let θS := selectorStockBudget α q0 ε t
  have hθS := selectorStockBudget_pos t hα hq0 hε
  let κ := q0*α/2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let D := forkQLimit κ
  obtain ⟨hD,hQ⟩ := forkQ_limit_spec hκ
  let K : ℕ := D+6
  have hK : (1:ℝ) ≤ K := by dsimp [K]; exact_mod_cast (show 1 ≤ D+6 by omega)
  let θ := withdrawalStockBudget α q0 ε t
  intro τ hτ
  let δS := selectorInputBudget α q0 ε t (τ/2)
  let nS := selectorOrder α q0 ε t (τ/2)
  have hδS := selectorInputBudget_pos t hα hq0 hε (half_pos hτ)
  let u := min δS (τ/2)
  have hu : 0 < u := lt_min hδS (by positivity)
  let δ := withdrawalInputBudget α q0 ε t τ
  have hδ := withdrawalInputBudget_pos t hα hq0 hε hτ
  intro V I _ H F W h2 hn hWlow hpool hroute
  change max (max nS ⌈32/κ⌉₊) ⌈1/δ⌉₊ ≤ Fintype.card V at hn
  have hSel := fixed_core_paid_selector_layer_explicit_with_core_incidence α q0 ε t
    hα hq0 ht ht3 hε (τ/2) (half_pos hτ) H F W h2
    ((le_max_left _ _).trans ((le_max_left _ _).trans hn)) hWlow hpool hroute
  intro X B _ _ r b hXG hX hB hr hb
  have hnR : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hδn : 1 ≤ δ*Fintype.card V := by
    have hcn : (⌈1/δ⌉₊:ℝ) ≤ Fintype.card V := by exact_mod_cast (le_max_right _ _).trans hn
    have hv := (Nat.le_ceil (1/δ)).trans hcn
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hv
  have hn32 : 32 ≤ κ*Fintype.card V := by
    have hcn : (⌈32/κ⌉₊:ℝ) ≤ Fintype.card V := by
      exact_mod_cast (le_max_right _ _).trans ((le_max_left _ _).trans hn)
    have hv := (Nat.le_ceil (32/κ)).trans hcn
    simpa only [mul_comm] using (div_le_iff₀ hκ).mp hv
  have hrF : (r:ℝ) ≤ forkEps κ*Fintype.card V :=
    hr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnR)
  have hbF : (b:ℝ) ≤ forkEps κ*Fintype.card V :=
    hb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnR)
  have hXE : X.edgeFinset ⊆ edges H := by
    intro e he
    exact mem_filter.mpr ⟨mem_univ _,SimpleGraph.edgeSet_mono hXG (by simpa using he)⟩
  have hXd : ∀ v, SparseEdge.degIn X.edgeFinset v ≤ r := by
    intro v
    change edeg X.edgeFinset v ≤ r
    rw [edeg_edgeFinset]
    exact hX v
  have hBd : ∀ v, SparseEdge.degIn B.edgeFinset v ≤ b := by
    intro v
    change edeg B.edgeFinset v ≤ b
    rw [edeg_edgeFinset]
    exact hB v
  obtain ⟨fk,hFS,hRfDeg⟩ := forks_on_core_pool W hκ (by
      intro v w hne k hk
      have hv := hpool v w hne k hk
      calc κ*Fintype.card V = q0*α*Fintype.card V/2 := by dsimp [κ]; ring
           _ ≤ _ := hv) h2 X.edgeFinset B.edgeFinset hXE hXd hBd hrF hbF hn32
  let Rf := forkUnion (XZ X.edgeFinset W) fk
  let X1 := (X.edgeFinset \ XZ X.edgeFinset W) ∪ QU fk (XZ X.edgeFinset W)
  let B1 := X.edgeFinset ∪ B.edgeFinset ∪ Rf
  let r1 := 3*r+forkQ κ r+4
  let b1 := b+3*r+forkQ κ r+4
  have hRfBas : Basal H F Rf := fork_union_basal hFS
  have hRfE : Rf ⊆ edges H := basal_subset_edges hRfBas
  have hRfAvoid : Disjoint Rf (X.edgeFinset ∪ B.edgeFinset) := by
    apply disjoint_left.mpr
    intro e he he'
    obtain ⟨f,hf,he⟩ := mem_biUnion.mp he
    exact disjoint_left.mp (hFS.2.2 f hf) he he'
  have hRfInc : ∀ e ∈ Rf, ∃ v ∈ e, v ∈ W := by
    intro e he
    obtain ⟨f,hf,he⟩ := mem_biUnion.mp he
    have hValid := (hFS.1 f hf).2
    change e ∈ (fk f).B ∪ (fk f).Q at he
    rcases mem_union.mp he with he | he
    · exact hValid.B_meets_W e he
    · exact hValid.Q_meets_W e he
  have hRfd : ∀ v, edeg Rf v ≤ 2*r+forkQ κ r+4 := hRfDeg
  obtain ⟨_,_,_,_,_,hX1W,hX1Deg⟩ := hFS.fork_L (L := ∅) (empty_subset _)
  change ∀ e ∈ X1, ∃ v ∈ e, v ∈ W at hX1W
  change ∀ v, SparseEdge.degIn X1 v ≤ SparseEdge.degIn X.edgeFinset v+SparseEdge.degIn Rf v at hX1Deg
  have hX1d : ∀ v, edeg X1 v ≤ r1 := by
    intro v
    have h1 := hX1Deg v
    have h2 : edeg X.edgeFinset v ≤ r := by rw [edeg_edgeFinset]; exact hX v
    have h3 := hRfd v
    change edeg X1 v ≤ edeg X.edgeFinset v+edeg Rf v at h1
    dsimp [r1]
    omega
  have hB1d : ∀ v, edeg B1 v ≤ b1 := by
    intro v
    have h1 := edeg_union_le (X.edgeFinset ∪ B.edgeFinset) Rf v
    have h2 := edeg_union_le X.edgeFinset B.edgeFinset v
    rw [edeg_edgeFinset,edeg_edgeFinset] at h2
    have h3 := hX v
    have h4 := hB v
    have h5 := hRfd v
    dsimp [B1,b1]
    omega
  have hQbound := hQ r
  change forkQ κ r ≤ D*(r+1) at hQbound
  have hsize : 3*r+forkQ κ r+4 ≤ K*(r+1) := by
    dsimp [K]
    nlinarith only [hQbound]
  have hδK : 2*(K:ℝ)*δ ≤ u := by
    have hd : δ ≤ u/(4*K) := (min_le_right _ _).trans (min_le_left _ _)
    have hx := (le_div_iff₀ (show (0:ℝ) < 4*K by positivity)).mp hd
    nlinarith [hK,hδ.le]
  have hδStock : 2*(K:ℝ)*δ ≤ θS/4 := by
    have hd : δ ≤ θS/(8*K) := (min_le_right _ _).trans (min_le_right _ _)
    have hx := (le_div_iff₀ (show (0:ℝ) < 8*K by positivity)).mp hd
    nlinarith
  have hNewBounds : ((3*r+forkQ κ r+4:ℕ):ℝ) ≤ u*Fintype.card V := by
    have hs : ((3*r+forkQ κ r+4:ℕ):ℝ) ≤ K*(r+1) := by exact_mod_cast hsize
    have hc := mul_le_mul_of_nonneg_left
      (show (r:ℝ)+1 ≤ 2*δ*Fintype.card V by linarith only [hr,hδn])
      (show (0:ℝ) ≤ K by positivity)
    have hd := mul_le_mul_of_nonneg_right hδK hnR
    push_cast at hs ⊢
    nlinarith only [hs,hc,hd]
  have hStockBounds : ((b+3*r+forkQ κ r+4:ℕ):ℝ) ≤ θS*Fintype.card V := by
    have hs : ((3*r+forkQ κ r+4:ℕ):ℝ) ≤ K*(r+1) := by exact_mod_cast hsize
    have hc := mul_le_mul_of_nonneg_left
      (show (r:ℝ)+1 ≤ 2*δ*Fintype.card V by linarith only [hr,hδn])
      (show (0:ℝ) ≤ K by positivity)
    have hd := mul_le_mul_of_nonneg_right hδStock hnR
    have hθsmall : θ ≤ θS/4 := min_le_right _ _
    have hθn := mul_le_mul_of_nonneg_right hθsmall hnR
    push_cast at hs ⊢
    nlinarith only [hs,hc,hd,hθn,hb]
  have hr1 : (r1:ℝ) ≤ δS*Fintype.card V := by
    have hhR : (r1:ℝ) ≤ ((3*r+forkQ κ r+4:ℕ):ℝ) := by
      exact_mod_cast (show r1 ≤ 3*r+forkQ κ r+4 by dsimp [r1]; omega)
    exact (hhR.trans hNewBounds).trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hnR)
  have hb1 : (b1:ℝ) ≤ θS*Fintype.card V := by
    simpa only [b1] using hStockBounds
  have hRfSmall : ∀ v, (edeg Rf v:ℝ) ≤ (τ/2)*Fintype.card V := by
    intro v
    have h1 : (edeg Rf v:ℝ) ≤ ((3*r+forkQ κ r+4:ℕ):ℝ) := by
      have hh := hRfd v
      exact_mod_cast (show edeg Rf v ≤ 3*r+forkQ κ r+4 by omega)
    exact (h1.trans hNewBounds).trans
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hnR)
  have hX1E : X1 ⊆ edges H := by
    apply union_subset
    · exact sdiff_subset.trans hXE
    · exact ((hFS.fork_modes (I' := XZ X.edgeFinset W) subset_rfl).2.1).trans hRfE
  have hDiagX : ∀ e ∈ X1, ¬ e.IsDiag := edges_diagonal_free hX1E
  have hDiagB : ∀ e ∈ B1, ¬ e.IsDiag := by
    intro e he
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · exact X.not_isDiag_of_mem_edgeSet (by simpa using he)
      · exact B.not_isDiag_of_mem_edgeSet (by simpa using he)
    · exact edges_diagonal_free hRfE e he
  let GX := SimpleGraph.fromEdgeSet (X1:Set (Sym2 V))
  let GB := SimpleGraph.fromEdgeSet (B1:Set (Sym2 V))
  have hGX : GX.edgeFinset = X1 := edgeFinset_fromEdges X1 hDiagX
  have hGB : GB.edgeFinset = B1 := edgeFinset_fromEdges B1 hDiagB
  have hGXmem : ∀ e, e ∈ GX.edgeSet ↔ e ∈ X1 := fun e => by
    simpa only [SimpleGraph.mem_edgeFinset] using (Finset.ext_iff.mp hGX e)
  have hGBmem : ∀ e, e ∈ GB.edgeSet ↔ e ∈ B1 := fun e => by
    simpa only [SimpleGraph.mem_edgeFinset] using (Finset.ext_iff.mp hGB e)
  have hGXW : ∀ v w, GX.Adj v w → v ∈ W ∨ w ∈ W := by
    intro v w hvw
    obtain ⟨a,ha,hW⟩ := hX1W s(v,w) hvw.1
    rcases Sym2.mem_iff.mp ha with rfl | rfl
    · exact Or.inl hW
    · exact Or.inr hW
  obtain ⟨σ,C,hAvoid,hBas,hEmpty,hRpInc,hDeg,hModes⟩ := hSel GX GB r1 b1
    (fromEdges_le_host hX1E) hGXW (fromEdges_degree_le X1 hDiagX hX1d)
    (fromEdges_degree_le B1 hDiagB hB1d) hr1 hb1
  letI : Fintype GX.edgeSet := GX.fintypeEdgeSet
  letI : Fintype GB.edgeSet := GB.fintypeEdgeSet
  let Rp := fuelU (univ \ W) σ ∪ C
  have hAvoid' : Disjoint Rp (X1 ∪ B1) := by
    apply disjoint_left.mpr
    intro e he he'
    apply disjoint_left.mp hAvoid he
    rcases mem_union.mp he' with he' | he'
    · exact mem_union_left _ (SimpleGraph.mem_edgeFinset.mpr ((hGXmem e).mpr he'))
    · exact mem_union_right _ (SimpleGraph.mem_edgeFinset.mpr ((hGBmem e).mpr he'))
  have hRpOld : Disjoint Rp (X.edgeFinset ∪ B.edgeFinset ∪ Rf) :=
    hAvoid'.mono_right subset_union_right
  have hRfRp : Disjoint Rf Rp := (hRpOld.mono_right subset_union_right).symm
  refine ⟨Rf ∪ Rp,disjoint_union_left.mpr ⟨hRfAvoid,hRpOld.mono_right subset_union_left⟩,
    hRfBas.union hBas hRfRp,?_,?_,?_,?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · exact hRfInc e he
    · exact hRpInc e he
  · intro v
    have h1 := edeg_union_le Rf Rp v
    have h2 := hRfSmall v
    have h3 := hDeg v
    have h1R : (edeg (Rf ∪ Rp) v:ℝ) ≤ edeg Rf v+edeg Rp v := by exact_mod_cast h1
    linarith only [h1R,h2,h3]
  · let Y0 := SelSimul.residual GX (univ \ W) σ ∅ ∪ C
    obtain ⟨hEq0,_,_,hIn0,hDeg0,_⟩ :=
      hModes ∅ (empty_subset _) (isPhysical_empty H F)
    have hY0Rp : Y0 ⊆ Rp := by
      have hh : Rp = packEdges (packing GX (univ \ W) σ ∅) ∪ Y0 := by
        simpa only [union_empty] using hEq0
      rw [hh]
      exact subset_union_right
    refine ⟨Y0,hEmpty,hY0Rp.trans subset_union_right,hIn0,?_⟩
    intro v
    exact (hDeg0 v).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hτ]) hnR)
  · intro L hL hphys
    let I0 := L ∩ XZ X.edgeFinset W
    let L1 := (L \ I0) ∪ QU fk I0
    let Pf := (Rf \ QU fk I0) ∪ I0
    obtain ⟨hfEq,hfDisj,_,hDiff,hL1,_,_⟩ := hFS.fork_L hL
    change L ∪ Rf = L1 ∪ Pf at hfEq
    change Disjoint L1 Pf at hfDisj
    have hL1Phys : IsPhysical H F L1 := SelectorEntry.physical_of_difference hphys hDiff
    obtain ⟨hsEq,hsDisj,hPs,hYIn,hYDeg,hYP⟩ := hModes L1
      (fun e he => SimpleGraph.mem_edgeFinset.mpr ((hGXmem e).mpr (hL1 he))) hL1Phys
    let Ps := packEdges (packing GX (univ \ W) σ L1)
    let Y := SelSimul.residual GX (univ \ W) σ L1 ∪ C
    change Rp ∪ L1 = Ps ∪ Y at hsEq
    change Disjoint Ps Y at hsDisj
    have hPf : Basal H F Pf := fork_mode_basal hFS hL
    have hPfSub : Pf ⊆ L ∪ Rf := by rw [hfEq]; exact subset_union_right
    have hRpLR : Disjoint Rp (L ∪ Rf) := hRpOld.mono_right (union_subset
      (hL.trans (subset_union_left.trans subset_union_left)) subset_union_right)
    have hRpPf := hRpLR.mono_right hPfSub
    have hUnionPf : Disjoint (Rp ∪ L1) Pf := disjoint_union_left.mpr ⟨hRpPf,hfDisj⟩
    have hPsSub : Ps ⊆ Rp ∪ L1 := by rw [hsEq]; exact subset_union_left
    have hYSub : Y ⊆ Rp ∪ L1 := by rw [hsEq]; exact subset_union_right
    have hPsPf := hUnionPf.mono_left hPsSub
    have hYPf := hUnionPf.mono_left hYSub
    refine ⟨Ps ∪ Pf,Y,?_,disjoint_union_left.mpr ⟨hsDisj,hYPf.symm⟩,
      hPs.union hPf hPsPf,hYIn,?_,hYP⟩
    · calc (Rf ∪ Rp) ∪ L = (L ∪ Rf) ∪ Rp := by ac_rfl
           _ = (L1 ∪ Pf) ∪ Rp := by rw [hfEq]
           _ = (Rp ∪ L1) ∪ Pf := by ac_rfl
           _ = (Ps ∪ Y) ∪ Pf := by rw [hsEq]
           _ = (Ps ∪ Pf) ∪ Y := by ac_rfl
    · intro v
      exact (hYDeg v).trans (mul_le_mul_of_nonneg_right (by linarith only [hτ]) hnR)



#print axioms fixed_core_paid_selector_layer_explicit_with_core_incidence
#print axioms fixed_core_positive_withdrawal_explicit_with_core_incidence
end TypedTriangle.CorePaid.Explicit
namespace TypedTriangle.Vortex.Explicit
open CorePaid CorePaid.Explicit BasalIncidence SelSimul
theorem uniform_fixed_window_withdrawal_explicit_with_core_incidence {I : Type}
    (F : Set (Multiset I)) (α q ε : ℝ) (t : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hε : 0 < ε)
    (ht : Odd t) (ht3 : 3 ≤ t) :
    ∀ τ : ℝ, 0 < τ →
      ∀ {V : Type} [Fintype V] (H : Host V I) (W : Finset V),
      IsPhysical H F (edges H) → withdrawalOrder α q ε t τ ≤ Fintype.card V →
      q * Fintype.card V / 2 ≤ W.card →
      (∀ u v : V, u ≠ v → ∀ k : I,
        ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
        q * α * Fintype.card V / 2 ≤ ((commonNbrs H k u v) ∩ W).card) →
      S07V27.RouteProp H.G H.lab F t ε W →
      ∀ (D : Finset (Finset V)) (T : Finset (Sym2 V)) (r b : ℕ),
        cover D ⊆ edges H → T ⊆ edges H →
        (∀ v, degIn (cover D) v ≤ r) →
        (∀ v, degIn T v ≤ b) →
        (r : ℝ) ≤ withdrawalInputBudget α q ε t τ * Fintype.card V →
        (b : ℝ) ≤ withdrawalStockBudget α q ε t * Fintype.card V →
        ∃ R : Finset (Sym2 V),
          Disjoint R (cover D ∪ T) ∧ Basal H F R ∧
          (∀ e ∈ R, ∃ v ∈ e, v ∈ W) ∧
          (∀ v, (edeg R v : ℝ) ≤ τ * Fintype.card V) ∧
          (∃ Y0 : Finset (Sym2 V), Basal H F Y0 ∧ Y0 ⊆ R ∧
            (∀ e ∈ Y0, ∀ v ∈ e, v ∈ W) ∧
            ∀ v, (edeg Y0 v : ℝ) ≤ τ * Fintype.card V) ∧
          ∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
            ∃ Ps Y : Finset (Sym2 V),
              R ∪ L = Ps ∪ Y ∧ Disjoint Ps Y ∧ Basal H F Ps ∧
              (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
              (∀ v, (edeg Y v : ℝ) ≤ τ * Fintype.card V) ∧
              IsPhysical H F Y := by
  intro τ hτ
  intro V _ H W h2 hn hW hpool hroute D T r b hD hT hdD hdT hr hb
  let X := SimpleGraph.fromEdgeSet (cover D : Set (Sym2 V))
  let B := SimpleGraph.fromEdgeSet (T : Set (Sym2 V))
  letI : DecidableRel X.Adj := Classical.decRel _
  letI : DecidableRel B.Adj := Classical.decRel _
  letI : Fintype X.edgeSet := X.fintypeEdgeSet
  letI : Fintype B.edgeSet := B.fintypeEdgeSet
  have hXmem (e : Sym2 V) : e ∈ X.edgeSet ↔ e ∈ cover D := by
    simp only [X, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe,
      Sym2.mem_diagSet]
    exact ⟨And.left, fun he => ⟨he, edges_diagonal_free hD e he⟩⟩
  have hBmem (e : Sym2 V) : e ∈ B.edgeSet ↔ e ∈ T := by
    simp only [B, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe,
      Sym2.mem_diagSet]
    exact ⟨And.left, fun he => ⟨he, edges_diagonal_free hT e he⟩⟩
  have hXd : ∀ v, X.degree v ≤ r := by
    intro v
    have hv := fromEdges_degree_le _ (edges_diagonal_free hD) hdD v
    convert hv using 1 <;> congr 2 <;> apply Subsingleton.elim
  have hBd : ∀ v, B.degree v ≤ b := by
    intro v
    have hv := fromEdges_degree_le _ (edges_diagonal_free hT) hdT v
    convert hv using 1 <;> congr 2 <;> apply Subsingleton.elim
  obtain ⟨R,hdis,hbasal,hInc,hdeg,hY0,hMode⟩ := CorePaid.Explicit.fixed_core_positive_withdrawal_explicit_with_core_incidence α q ε t
    hα hq ht ht3 hε τ hτ H F W h2 hn hW hpool hroute
    X B r b (fromEdges_le_host hD) hXd hBd hr hb
  refine ⟨R,?_,hbasal,hInc,hdeg,hY0,?_⟩
  · apply disjoint_left.mpr
    intro e heR he
    apply disjoint_left.mp hdis heR
    rcases mem_union.mp he with he | he
    · apply mem_union_left
      simpa only [SimpleGraph.mem_edgeFinset] using (hXmem e).mpr he
    · apply mem_union_right
      simpa only [SimpleGraph.mem_edgeFinset] using (hBmem e).mpr he
  · intro L hL hphys
    apply hMode L ?_ hphys
    intro e he
    simpa only [SimpleGraph.mem_edgeFinset] using (hXmem e).mpr (hL he)

/- Incidence with a disjoint core excludes every edge internal to the
protected vertex set, regardless of the degree of that internal edge set. -/

#print axioms uniform_fixed_window_withdrawal_explicit_with_core_incidence
end TypedTriangle.Vortex.Explicit

/-! Numerical resource component: ExplicitFixedWindowResources. -/
namespace TypedTriangle.Vortex.Explicit
open CorePaid BasalIncidence SelSimul

def resourceStockBudget (α C : ℝ) : ℝ := BasalIncidence.Explicit.rawStockAvoidBudget (1/C) C α
def resourceTerminalBudget (α C : ℝ) (h : ℕ) (αW qW εW η : ℝ) (t : ℕ) : ℝ :=
  min (BasalIncidence.Explicit.rawStockBudget (1/C) C α h)
    (min (CorePaid.Explicit.withdrawalStockBudget αW qW εW t) (η*qW/16))
def resourceOutputBudget (qW η τcap : ℝ) : ℝ := min (η*qW/16) τcap
def resourceInputBudget (αW qW εW η : ℝ) (t : ℕ) (ρcap τcap : ℝ) : ℝ :=
  let τ := resourceOutputBudget qW η τcap
  min (CorePaid.Explicit.withdrawalInputBudget αW qW εW t τ/4) (min τ ρcap)
def resourceCompletion (α αW qW εW η : ℝ) (t : ℕ) (ρcap τcap : ℝ) : ℝ :=
  BasalIncidence.Explicit.rawStockCompletion α (resourceInputBudget αW qW εW η t ρcap τcap)
def resourceOrder (α C : ℝ) (h : ℕ) (αW qW εW η : ℝ) (t : ℕ) (ρcap τcap : ℝ) : ℕ :=
  let τ := resourceOutputBudget qW η τcap
  let δ := CorePaid.Explicit.withdrawalInputBudget αW qW εW t τ
  max (BasalIncidence.Explicit.rawStockOrder (1/C) C α (resourceInputBudget αW qW εW η t ρcap τcap))
    (max (CorePaid.Explicit.withdrawalOrder αW qW εW t τ) ⌈4/δ⌉₊)

theorem resource_parameters_pos (α C : ℝ) (h : ℕ) (αW qW εW η : ℝ) (t : ℕ)
    (ρcap τcap : ℝ) (hα : 0 < α) (hC : 1 ≤ C) (hαW : 0 < αW)
    (hqW : 0 < qW) (hεW : 0 < εW) (hη : 0 < η) (hρcap : 0 < ρcap) (hτcap : 0 < τcap) :
    0 < resourceStockBudget α C ∧ 0 < resourceTerminalBudget α C h αW qW εW η t ∧
      0 < resourceInputBudget αW qW εW η t ρcap τcap ∧
      0 < resourceCompletion α αW qW εW η t ρcap τcap ∧
      0 < resourceOutputBudget qW η τcap := by
  have hCp : 0 < C := by linarith
  have ha : 0 < 1/C := by positivity
  have hab : 1/C ≤ C := (div_le_iff₀ hCp).mpr (by nlinarith)
  have hRaw := BasalIncidence.Explicit.raw_stock_windows_pos (1/C) C α h ha hab hα
  have hθ := CorePaid.Explicit.withdrawalStockBudget_pos t hαW hqW hεW
  have hτ : 0 < resourceOutputBudget qW η τcap := lt_min (by positivity) hτcap
  have hδ := CorePaid.Explicit.withdrawalInputBudget_pos t hαW hqW hεW hτ
  have hρ : 0 < resourceInputBudget αW qW εW η t ρcap τcap :=
    lt_min (by positivity) (lt_min hτ hρcap)
  exact ⟨hRaw.2.2,lt_min hRaw.1 (lt_min hθ (by positivity)),hρ,
    BasalIncidence.Explicit.raw_stock_completion_pos hα hρ,hτ⟩

theorem resource_rate_caps (αW qW εW η : ℝ) (t : ℕ) (ρcap τcap : ℝ) :
    resourceInputBudget αW qW εW η t ρcap τcap ≤ ρcap ∧
      resourceOutputBudget qW η τcap ≤ τcap ∧
      resourceInputBudget αW qW εW η t ρcap τcap ≤ resourceOutputBudget qW η τcap :=
  ⟨(min_le_right _ _).trans (min_le_right _ _),min_le_right _ _,
    (min_le_right _ _).trans (min_le_left _ _)⟩

theorem fixed_window_resources_explicit_protecting_vertices {I : Type}
    (F : Set (Multiset I)) (α C : ℝ) (h : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) :
    ∀ (αW qW εW η : ℝ) (t : ℕ),
      0 < αW → 0 < qW → 0 < εW → 0 < η → Odd t → 3 ≤ t →
    ∀ ρcap τcap : ℝ, 0 < ρcap → 0 < τcap →
    ∀ {V : Type} [Fintype V]
          (H : Host V I) (φ : Finset V → ℝ) (W : Finset V)
          (U : Finset V) (T S : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT dS : ℕ),
          resourceOrder α C h αW qW εW η t ρcap τcap ≤ Fintype.card V → IsDiffuseSeed H F C φ →
          IsPhysical H F (edges H) →
          CommonNbrCond H F α → HingeCond H F α h →
          qW * Fintype.card V / 2 ≤ W.card →
          (∀ u v : V, u ≠ v → ∀ k : I,
            ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
            qW * αW * Fintype.card V / 2 ≤
              ((commonNbrs H k u v) ∩ W).card) →
          S07V27.RouteProp H.G H.lab F t εW W →
          IsDecomposition H F T DT → Disjoint T S →
          Disjoint W U → (∀ e ∈ S, ∀ v ∈ e, v ∈ U) →
          (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ resourceStockBudget α C*Fintype.card V →
          (∀ v, degIn T v ≤ dT) →
          (dT : ℝ) ≤ resourceTerminalBudget α C h αW qW εW η t * Fintype.card V →
          ∃ (D : Finset (Finset V)) (R : Finset (Sym2 V)),
            IsDecomposition H F (cover D) D ∧
            Disjoint (cover D) (T ∪ S) ∧
            (∀ v, (degIn (cover D) v : ℝ) < resourceInputBudget αW qW εW η t ρcap τcap * Fintype.card V) ∧
            (∀ u v, H.G.Adj u v → resourceCompletion α αW qW εW η t ρcap τcap * Fintype.card V ≤ (good H F D u v).card) ∧
            Disjoint R (cover D ∪ T) ∧ Basal H F R ∧
            (∀ e ∈ R, ∃ v ∈ e, v ∈ W) ∧ Disjoint R S ∧
            (∀ v, (edeg R v : ℝ) ≤ resourceOutputBudget qW η τcap * Fintype.card V) ∧
            (∀ v, (degIn ((cover D ∪ R) ∪ T) v : ℝ) ≤ η * W.card) ∧
            (∃ Y0 : Finset (Sym2 V), Basal H F Y0 ∧ Y0 ⊆ R ∧
              (∀ e ∈ Y0, ∀ v ∈ e, v ∈ W) ∧
              ∀ v, (edeg Y0 v : ℝ) ≤ resourceOutputBudget qW η τcap * Fintype.card V) ∧
            ∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
              ∃ Ps Y : Finset (Sym2 V),
                R ∪ L = Ps ∪ Y ∧ Disjoint Ps Y ∧ Basal H F Ps ∧
                (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
                (∀ v, (edeg Y v : ℝ) ≤ resourceOutputBudget qW η τcap * Fintype.card V) ∧
                IsPhysical H F Y := by
  have hCp : 0 < C := by linarith
  have ha : 0 < 1/C := by positivity
  have hab : 1/C ≤ C := (div_le_iff₀ hCp).mpr (by nlinarith)
  let θS := BasalIncidence.Explicit.rawStockBudget (1/C) C α h
  have hεR := (BasalIncidence.Explicit.raw_stock_windows_pos (1/C) C α h ha hab hα).2.1
  intro αW qW εW η t hαW hqW hεW hη ht ht3 ρcap τcap hρcap hτcap
  let θP := CorePaid.Explicit.withdrawalStockBudget αW qW εW t
  let θT := resourceTerminalBudget α C h αW qW εW η t
  let τ := resourceOutputBudget qW η τcap
  have hτ : 0 < τ := lt_min (by positivity) hτcap
  let δ := CorePaid.Explicit.withdrawalInputBudget αW qW εW t τ
  let nSel := CorePaid.Explicit.withdrawalOrder αW qW εW t τ
  have hδ := CorePaid.Explicit.withdrawalInputBudget_pos t hαW hqW hεW hτ
  let ρ := resourceInputBudget αW qW εW η t ρcap τcap
  have hρ : 0 < ρ := lt_min (by positivity) (lt_min hτ hρcap)
  let nStock := BasalIncidence.Explicit.rawStockOrder (1/C) C α ρ
  intro V _ H φ W U T S DT dT dS hn hSeed hPhys h3 h4 hW hpool hroute
    hT hTS hWU hSU hSd hScap hTd hTcap
  change max nStock (max nSel ⌈4/δ⌉₊) ≤ Fintype.card V at hn
  have hnStock : nStock ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnSel : nSel ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnδ : ⌈4/δ⌉₊ ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hδn : 4 ≤ δ*Fintype.card V := by
    have hh : (4/δ:ℝ) ≤ Fintype.card V :=
      (Nat.le_ceil _).trans (by exact_mod_cast hnδ)
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hh
  have hμ : ∀ U, IsAllowed H F U →
      (1/C)/Fintype.card V ≤ φ U ∧ φ U ≤ C/Fintype.card V := by
    intro U hU
    have hh := hSeed.1 U hU
    constructor
    · convert hh.1 using 1 <;> ring
    · exact hh.2
  have hTsub : T ⊆ edges H := basal_subset_edges ⟨DT,hT⟩
  have hθSbound : (dT:ℝ) ≤ θS*Fintype.card V :=
    hTcap.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  obtain ⟨D,hD,hDT,hDd,hSupply⟩ := BasalIncidence.Explicit.reserve_from_raw_profile_explicit F (1/C) C α h ha hab hα ρ hρ
      H φ T S DT dT dS hnStock h3 h4 hμ
    (by intro e he; have he' : e ∈ H.G.edgeSet := by simpa [edges] using he
        simpa [IsDiffuseSeed.bdry_eq_one hSeed he'] using hεR.le)
    hTsub hT hTS hTd hθSbound hSd hScap
  let r := ⌈ρ*Fintype.card V⌉₊
  have hr : (r:ℝ) ≤ δ*Fintype.card V := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ ρ*Fintype.card V by positivity)
    have hρδ : ρ ≤ δ/4 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hρδ
      (show (0:ℝ) ≤ Fintype.card V by positivity)]
  have hDdNat : ∀ v, degIn (cover D) v ≤ r := by
    intro v
    exact_mod_cast (hDd v).le.trans (Nat.le_ceil _)
  have hθPbound : (dT:ℝ) ≤ θP*Fintype.card V :=
    hTcap.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_left _ _)) (by positivity))
  obtain ⟨R,hRdis,hR,hRinc,hRd,hY0,hMode⟩ :=
    uniform_fixed_window_withdrawal_explicit_with_core_incidence F αW qW εW t
      hαW hqW hεW ht ht3 τ hτ H W hPhys hnSel hW hpool hroute D T r dT
      (basal_subset_edges ⟨D,hD⟩) hTsub hDdNat hTd hr hθPbound
  have hRS : Disjoint R S := disjoint_of_core_incidence W U R S hWU hRinc hSU
  have hF0 : ∀ v, (degIn ((cover D ∪ R) ∪ T) v : ℝ) ≤ η*W.card := by
    intro v
    have hu : (degIn ((cover D ∪ R) ∪ T) v : ℝ) ≤
        degIn (cover D) v + degIn R v + degIn T v := by
      have ha := edeg_union_le (cover D ∪ R) T v
      have hb := edeg_union_le (cover D) R v
      change degIn ((cover D ∪ R) ∪ T) v ≤ degIn (cover D ∪ R) v + degIn T v at ha
      change degIn (cover D ∪ R) v ≤ degIn (cover D) v + degIn R v at hb
      exact_mod_cast (show degIn ((cover D ∪ R) ∪ T) v ≤
        degIn (cover D) v + degIn R v + degIn T v by omega)
    have hx := (hDd v).le
    have hy := hRd v
    change (degIn R v : ℝ) ≤ τ * Fintype.card V at hy
    have hz : (degIn T v : ℝ) ≤ dT := by exact_mod_cast hTd v
    have hρτ : ρ ≤ τ := (min_le_right _ _).trans (min_le_left _ _)
    have hτbound : τ ≤ η*qW/16 := min_le_left _ _
    have hTbound : θT ≤ η*qW/16 :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hθTn := mul_le_mul_of_nonneg_right hTbound
      (show (0:ℝ) ≤ Fintype.card V by positivity)
    have hρτn := mul_le_mul_of_nonneg_right hρτ
      (show (0:ℝ) ≤ Fintype.card V by positivity)
    have hτn := mul_le_mul_of_nonneg_right hτbound
      (show (0:ℝ) ≤ Fintype.card V by positivity)
    have hWn := mul_le_mul_of_nonneg_left hW hη.le
    nlinarith [hu,hx,hy,hz,hTcap,hθTn,hρτn,hτn,hWn]
  exact ⟨D,R,hD,hDT,hDd,hSupply,
    hRdis,hR,hRinc,hRS,hRd,hF0,hY0,hMode⟩


#print axioms fixed_window_resources_explicit_protecting_vertices
end TypedTriangle.Vortex.Explicit

