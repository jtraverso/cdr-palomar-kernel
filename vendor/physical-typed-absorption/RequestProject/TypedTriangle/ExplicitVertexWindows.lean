module
public import RequestProject.TypedTriangle.UniformVertexChains
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false

namespace TypedTriangle.ExplicitGeometry

def deletionBudget (α : ℝ) (h : ℕ) : ℝ :=
  min (1 / 2) (α / (4 * 2 ^ Nat.choose (h + 1) 2))

def nestedBudget (α : ℝ) (h : ℕ) : ℝ :=
  min (deletionBudget α h) (α / (128 * 2 ^ Nat.choose (h + 1) 2))

def nestedOrder (α : ℝ) (h : ℕ) : ℕ :=
  ⌈(16 + 16 * h * (2 : ℝ) ^ Nat.choose h 2) / α⌉₊ + 1

theorem deletionBudget_spec {α : ℝ} (hα : 0 < α) (h : ℕ) :
    0 < deletionBudget α h ∧ deletionBudget α h ≤ 1 / 2 ∧
      ∀ {n z : ℝ}, 0 ≤ n → z ≤ deletionBudget α h * n →
        z ≤ α * n / 2 ∧ z * 2 ^ Nat.choose (h + 1) 2 ≤ α / 2 * n := by
  let M : ℝ := 2 ^ Nat.choose (h + 1) 2
  have hM : 1 ≤ M := one_le_pow₀ (by norm_num)
  refine ⟨by unfold deletionBudget; positivity, min_le_left _ _, ?_⟩
  intro n z hn hz
  have hzM : z * M ≤ α * n / 4 := by
    have hδ : deletionBudget α h ≤ α / (4 * M) := min_le_right _ _
    have h1 := mul_le_mul_of_nonneg_right hδ hn
    calc
      z * M ≤ (α / (4 * M) * n) * M :=
        mul_le_mul_of_nonneg_right (hz.trans h1) (by positivity)
      _ = α * n / 4 := by field_simp
  have hz0 : z ≤ α * n / 4 := by
    by_cases hnon : 0 ≤ z
    · exact (le_mul_of_one_le_right hnon hM).trans hzM
    · exact (lt_of_not_ge hnon).le.trans (by positivity)
  have hαn : 0 ≤ α * n := mul_nonneg hα.le hn
  change z ≤ α * n / 2 ∧ z * M ≤ α / 2 * n
  constructor <;> linarith

theorem nestedBudget_pos {α : ℝ} (hα : 0 < α) (h : ℕ) :
    0 < nestedBudget α h := by
  exact lt_min (deletionBudget_spec hα h).1 (by positivity)

/-- The original nested-deletion windows at a specified order and tolerance. -/
theorem nested_windows_explicit (α : ℝ) (h : ℕ) (hα : 0 < α)
    {V : Type} [Fintype V] (A B : Finset V)
    (hn : nestedOrder α h ≤ Fintype.card V)
    (hA : (A.card : ℝ) ≤ nestedBudget α h * Fintype.card V)
    (hB : (B.card : ℝ) ≤ nestedBudget α h * Fintype.card V) :
    (A.card : ℝ) ≤ α * Fintype.card V / 2 ∧
      (A.card : ℝ) * 2 ^ Nat.choose (h + 1) 2 ≤ α / 2 * Fintype.card V ∧
      (B.card : ℝ) + 2 < (α / 2) * Fintype.card (Survivors A) ∧
      ((B.card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤ α / 4 * Fintype.card (Survivors A) := by
  let P : ℝ := 2 ^ Nat.choose h 2
  let Q : ℝ := 2 ^ Nat.choose (h + 1) 2
  have hP : 1 ≤ P := one_le_pow₀ (by norm_num)
  have hQ : 1 ≤ Q := one_le_pow₀ (by norm_num)
  have hPQ : P ≤ Q := pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 (by omega))
  let n : ℝ := Fintype.card V
  have hn0 : 0 ≤ n := by positivity
  have hAδ : (A.card : ℝ) ≤ deletionBudget α h * n :=
    hA.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
  obtain ⟨hδ, hδhalf, hδbudget⟩ := deletionBudget_spec hα h
  obtain ⟨hA3, hA4⟩ := hδbudget hn0 hAδ
  have hhalf : (A.card : ℝ) ≤ n / 2 := by
    have := mul_le_mul_of_nonneg_right hδhalf hn0
    linarith
  have hcard : (Fintype.card (Survivors A) : ℝ) + A.card = n := by
    dsimp [n]
    exact_mod_cast card_survivors_add_card A
  have hN : n / 2 ≤ (Fintype.card (Survivors A) : ℝ) := by linarith
  have hnlarge : 16 + 16 * h * P < α * n := by
    have hc : (16 + 16 * h * P) / α ≤ (⌈(16 + 16 * h * P) / α⌉₊ : ℝ) := Nat.le_ceil _
    have hcn : (nestedOrder α h : ℝ) ≤ n := by
      change (nestedOrder α h : ℝ) ≤ (Fintype.card V : ℝ)
      exact Nat.cast_le.mpr hn
    dsimp [nestedOrder] at hcn
    push_cast at hcn
    have hd : (16 + 16 * h * P) / α < n := by linarith
    have := (div_lt_iff₀ hα).mp hd
    linarith
  have hn16 : 16 ≤ α * n := by
    have : 0 ≤ (h : ℝ) * P := by positivity
    nlinarith
  have hhP : (h : ℝ) * P ≤ α * n / 16 := by linarith
  have hzQ : (B.card : ℝ) * Q ≤ α * n / 128 := by
    have hcap : nestedBudget α h ≤ α / (128 * Q) := min_le_right _ _
    have h1 := hB.trans (mul_le_mul_of_nonneg_right hcap hn0)
    calc
      (B.card : ℝ) * Q ≤ (α / (128 * Q) * n) * Q :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = α * n / 128 := by field_simp
  have hzP : (B.card : ℝ) * P ≤ α * n / 64 := by
    have h1 := mul_le_mul_of_nonneg_left hPQ (show (0 : ℝ) ≤ B.card by positivity)
    have h2 : 0 ≤ α * n := mul_nonneg hα.le hn0
    linarith
  obtain ⟨hw1, hw2⟩ := vertex_deletion_windows hα
    (show (0 : ℝ) ≤ B.card by positivity) hP hN hn16 hzP hhP
  exact ⟨hA3, hA4, hw1, hw2⟩

#print axioms deletionBudget_spec
#print axioms nested_windows_explicit
end TypedTriangle.ExplicitGeometry
