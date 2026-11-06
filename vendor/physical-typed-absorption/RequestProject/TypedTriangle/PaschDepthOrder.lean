module
public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch

def paschDepthSeed (A : ℕ) : ℕ := 2^(A+64)

/-- An explicit order for quartic functions of the logarithmic depth.
Its enormous value is never evaluated by the proof. -/
def paschDepthOrder (A : ℕ) : ℕ := 2^(4*paschDepthSeed A)

theorem nat_le_two_pow (A : ℕ) : A ≤ 2^A := by
  induction A with
  | zero => norm_num
  | succ A ih =>
    rw [pow_succ]
    have hp : 0 < (2 : ℕ)^A := by positivity
    omega

theorem depth_seed_linear_bound (A : ℕ) : 5*A+268 ≤ paschDepthSeed A := by
  unfold paschDepthSeed
  induction A with
  | zero => norm_num
  | succ A ih =>
    have he : A+1+64 = (A+64)+1 := by omega
    rw [he,pow_succ]
    omega

theorem depth_seed_at_least_six (A : ℕ) : 6 ≤ paschDepthSeed A := by
  have hh := depth_seed_linear_bound A
  omega

theorem quartic_step_le_double (k : ℕ) (hk : 6 ≤ k) :
    (k+2)^4 ≤ 2*(k+1)^4 := by
  let x := (k : ℝ)
  have hx : (6 : ℝ) ≤ x := by dsimp only [x]; exact_mod_cast hk
  have hSq : (36 : ℝ) ≤ x^2 := by
    have hh := mul_nonneg (show (0 : ℝ) ≤ x-6 by linarith)
      (show (0 : ℝ) ≤ x+6 by linarith)
    nlinarith only [hh]
  have hFourth := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hSq)
  have hQuad := mul_nonneg (show (0 : ℝ) ≤ x-6 by linarith)
    (show (0 : ℝ) ≤ x+5 by linarith)
  have hh : (x+2)^4 ≤ 2*(x+1)^4 := by nlinarith only [hFourth,hQuad]
  dsimp only [x] at hh
  exact_mod_cast hh

theorem quartic_block_step (A k : ℕ) (hk : 6 ≤ k) :
    A*(4*(k+1)+4)^4 ≤ 2*(A*(4*k+4)^4) := by
  calc
    _ = (256*A)*(k+2)^4 := by ring
    _ ≤ (256*A)*(2*(k+1)^4) := Nat.mul_le_mul_left _ (quartic_step_le_double k hk)
    _ = _ := by ring

theorem quartic_depth_seed_base (A : ℕ) :
    A*(4*paschDepthSeed A+4)^4 ≤ 2^paschDepthSeed A := by
  let K := paschDepthSeed A
  have hK : 1 ≤ K := by have hh := depth_seed_at_least_six A; omega
  have hSize : 4*K+4 ≤ 8*K := by omega
  have hA := nat_le_two_pow A
  have hBound := Nat.mul_le_mul hA (Nat.pow_le_pow_left hSize 4)
  have hPower : (2^A)*(8*K)^4 = 2^(5*A+268) := by
    dsimp only [K,paschDepthSeed]
    rw [mul_pow,show (8 : ℕ)^4 = 2^12 by norm_num,←pow_mul,←pow_add,←pow_add]
    congr 1
    omega
  change A*(4*K+4)^4 ≤ 2^K
  calc
    _ ≤ (2^A)*(8*K)^4 := hBound
    _ = 2^(5*A+268) := hPower
    _ ≤ 2^K := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (depth_seed_linear_bound A)

theorem quartic_depth_bound_after_seed (A k : ℕ) (hk : paschDepthSeed A ≤ k) :
    A*(4*k+4)^4 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => exact quartic_depth_seed_base A
  | succ k hk ih =>
    have hs := quartic_block_step A k ((depth_seed_at_least_six A).trans hk)
    have hm := Nat.mul_le_mul_left 2 ih
    calc
      _ ≤ 2*(A*(4*k+4)^4) := hs
      _ ≤ 2*2^k := hm
      _ = _ := by rw [pow_succ]; omega

/-- This pays every polynomial eligibility cutoff up to logarithmic depth
while the current host remains above the fourth-root tracking cutoff. -/
theorem quartic_log_bound_at_explicit_order (A n j : ℕ)
    (hOrder : paschDepthOrder A ≤ n) (hj : j ≤ Nat.log 2 n) :
    A*(j+1)^4 ≤ Nat.sqrt (Nat.sqrt n) := by
  let d := Nat.log 2 n
  let k := d/4
  have hOrderPos : 0 < paschDepthOrder A := by unfold paschDepthOrder; positivity
  have hn : n ≠ 0 := by omega
  have hd : 4*paschDepthSeed A ≤ d := Nat.le_log_of_pow_le (by decide) hOrder
  have hk : paschDepthSeed A ≤ k := by dsimp only [k]; omega
  have hPoly := quartic_depth_bound_after_seed A k hk
  have hj' : j+1 ≤ 4*k+4 := by dsimp only [k,d]; omega
  have hExp : 4*k ≤ d := by dsimp only [k]; omega
  have hPow : (2^k)^4 ≤ n := by
    calc
      _ = 2^(4*k) := by rw [←pow_mul]; congr 1; omega
      _ ≤ 2^d := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hExp
      _ ≤ n := Nat.pow_log_le_self 2 hn
  have hRoot : 2^k ≤ Nat.sqrt (Nat.sqrt n) := by
    apply Nat.le_sqrt'.mpr
    apply Nat.le_sqrt'.mpr
    calc
      _ = (2^k)^4 := by ring
      _ ≤ n := hPow
  exact (Nat.mul_le_mul_left A (Nat.pow_le_pow_left hj' 4)).trans (hPoly.trans hRoot)

#print axioms nat_le_two_pow
#print axioms depth_seed_linear_bound
#print axioms depth_seed_at_least_six
#print axioms quartic_step_le_double
#print axioms quartic_block_step
#print axioms quartic_depth_seed_base
#print axioms quartic_depth_bound_after_seed
#print axioms quartic_log_bound_at_explicit_order
end TypedTriangle.Pasch
