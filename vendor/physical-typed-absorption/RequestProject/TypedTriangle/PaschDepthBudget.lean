module
public import RequestProject.TypedTriangle.PaschAdaptiveBudget
public import RequestProject.TypedTriangle.PaschDepthOrder
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch

theorem two_pow_mul_shrinking_host_le (m : ℕ → ℕ)
    (hShrink : ∀ j, 2*m (j+1) ≤ m j) (j : ℕ) : 2^j*m j ≤ m 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      2^(j+1)*m (j+1) = 2^j*(2*m (j+1)) := by rw [pow_succ]; ring
      _ ≤ 2^j*m j := Nat.mul_le_mul_left _ (hShrink j)
      _ ≤ m 0 := ih

theorem depth_le_log_of_positive_host (m : ℕ → ℕ)
    (hShrink : ∀ j, 2*m (j+1) ≤ m j) (j nRoot : ℕ)
    (hFirst : m 0 ≤ nRoot) (hCurrent : 0 < m j) : j ≤ Nat.log 2 nRoot := by
  have hPow : 2^j ≤ nRoot := by
    calc
      _ ≤ 2^j*m j := le_mul_of_one_le_right (Nat.zero_le _) (by omega)
      _ ≤ m 0 := two_pow_mul_shrinking_host_le m hShrink j
      _ ≤ nRoot := hFirst
  exact Nat.le_log_of_pow_le (by decide) hPow

theorem eligibility_polynomial_below_tracking_cutoff (m : ℕ → ℕ)
    (hShrink : ∀ j, 2*m (j+1) ≤ m j) (j A nRoot : ℕ)
    (hFirst : m 0 ≤ nRoot) (hOrder : paschDepthOrder A ≤ nRoot)
    (hTracking : Nat.sqrt (Nat.sqrt nRoot) < m j) : A*(j+1)^4 < m j := by
  have hj := depth_le_log_of_positive_host m hShrink j nRoot hFirst (by omega)
  exact (quartic_log_bound_at_explicit_order A nRoot j hOrder hj).trans_lt hTracking

theorem accumulated_codegree_linear_bound (L : ℕ → ℕ) (Lbase K : ℕ)
    (hBase : L 0 ≤ Lbase) (hStep : ∀ j, L (j+1) ≤ L j+K) (j shift : ℕ) :
    L j+shift ≤ (Lbase+K+shift)*(j+1) := by
  have hh : ∀ i, L i ≤ Lbase+K*i := by
    intro i
    induction i with
    | zero => simpa using hBase
    | succ i ih => have hs := hStep i; nlinarith only [ih,hs]
  have hj := hh j
  nlinarith only [hj,Nat.zero_le (Lbase*j),Nat.zero_le (shift*j)]

theorem depth_succ_le_two_pow (j : ℕ) : j+1 ≤ 2^j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ]
    omega

/-- Cubic growth of the accumulated pair codegree is paid by the actual
1/16 contraction of host orders, uniformly in the length of the run. -/
theorem shrinking_cubic_depth_sum_le (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hShrink : ∀ j, a (j+1) ≤ a j/16) (N : ℕ) :
    (∑ j ∈ range N, ((j : ℝ)+1)^3*a j) ≤ 2*a 0 := by
  let b := fun j : ℕ => (8 : ℝ)^j*a j
  have hb : ∀ j, 0 ≤ b j := fun j => mul_nonneg (by positivity) (ha j)
  have hB : ∀ j, b (j+1) ≤ b j/2 := by
    intro j
    have hh := mul_le_mul_of_nonneg_left (hShrink j) (show (0 : ℝ) ≤ 8^j by positivity)
    dsimp only [b]
    rw [pow_succ]
    nlinarith only [hh]
  have hSum : ∀ M, (∑ j ∈ range M, b j) ≤ 2*(b 0-b M) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [sum_range_succ]
      have hh := hB M
      linarith only [ih,hh]
  have hPoint : ∀ j : ℕ, ((j : ℝ)+1)^3 ≤ (8 : ℝ)^j := by
    intro j
    have hj : (j : ℝ)+1 ≤ (2 : ℝ)^j := by exact_mod_cast depth_succ_le_two_pow j
    calc
      _ ≤ ((2 : ℝ)^j)^3 := pow_le_pow_left₀ (by positivity) hj 3
      _ = (8 : ℝ)^j := by rw [←pow_mul,Nat.mul_comm j 3,pow_mul]; norm_num
  calc
    _ ≤ ∑ j ∈ range N, b j := sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (hPoint j) (ha j))
    _ ≤ 2*(b 0-b N) := hSum N
    _ ≤ 2*a 0 := by have hh := hb N; dsimp only [b] at *; simp only [pow_zero,one_mul] at *; linarith

theorem adaptive_cubic_cost_sum_bound (a : ℕ → ℝ) (D nRoot q : ℝ)
    (hD : 0 ≤ D) (hnRoot : 0 ≤ nRoot) (ha : ∀ j, 0 ≤ a j)
    (hShrink : ∀ j, a (j+1) ≤ a j/16) (hFirst : a 0 ≤ 2*q*nRoot) (N : ℕ) :
    (∑ j ∈ range N, D*nRoot*((j : ℝ)+1)^3*a j) ≤ 4*D*q*nRoot^2 := by
  have hs := shrinking_cubic_depth_sum_le a ha hShrink N
  calc
    _ = (D*nRoot)*(∑ j ∈ range N, ((j : ℝ)+1)^3*a j) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ (D*nRoot)*(2*a 0) := mul_le_mul_of_nonneg_left hs (mul_nonneg hD hnRoot)
    _ ≤ (D*nRoot)*(2*(2*q*nRoot)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hFirst (by norm_num)) (mul_nonneg hD hnRoot)
    _ = _ := by ring

#print axioms depth_succ_le_two_pow
#print axioms two_pow_mul_shrinking_host_le
#print axioms depth_le_log_of_positive_host
#print axioms eligibility_polynomial_below_tracking_cutoff
#print axioms accumulated_codegree_linear_bound
#print axioms shrinking_cubic_depth_sum_le
#print axioms adaptive_cubic_cost_sum_bound
end TypedTriangle.Pasch
