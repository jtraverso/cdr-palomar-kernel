/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexPaidPreparedOrder
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace TypedTriangle.Vortex.ExplicitPaid

def latticeBudget (α : ℝ) (h : ℕ) : ℝ := α / (8 * 2 ^ h.choose 2)
def latticeOrder (α : ℝ) : ℕ := ⌈4 / α⌉₊ + 1
def hingeBudget (α : ℝ) (h : ℕ) : ℝ := α / (64 * 2 ^ h.choose 2)
def geometryBudget (α : ℝ) (h : ℕ) : ℝ := min (α / 4) (hingeBudget α h)
def geometryOrder (α : ℝ) (h : ℕ) : ℕ := ⌈128 * (h + 2) * 2 ^ h.choose 2 / α⌉₊ + 1

theorem latticeBudget_pos {α : ℝ} (h : ℕ) (hα : 0 < α) : 0 < latticeBudget α h := by
  unfold latticeBudget
  positivity

theorem geometryBudget_pos {α : ℝ} (h : ℕ) (hα : 0 < α) : 0 < geometryBudget α h := by
  unfold geometryBudget hingeBudget
  positivity

/-- The original sparse-deletion lattice windows with their specified constants. -/
theorem sparse_edge_deletion_host_explicit (α : ℝ) (h : ℕ) (hα : 0 < α)
    (V I : Type) [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (hn : latticeOrder α ≤ Fintype.card V)
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h)
    (B : Finset (Sym2 V))
    (hdeg : ∀ x, (((B.filter (fun e => x ∈ e)).card : ℕ) : ℝ) ≤
      latticeBudget α h * Fintype.card V) (y : Sym2 V → ℤ) :
    y ∈ lattice (subHost H (edges H \ B)) F ↔
      y ∈ lattice H F ∧ ∀ e ∈ B,y e = 0 := by
  let M : ℝ := 2 ^ h.choose 2
  have hM1 : (1 : ℝ) ≤ M := one_le_pow₀ (by norm_num)
  let n : ℝ := Fintype.card V
  have hnα : 4 / α < n := by
    have h1 : (4 / α) ≤ ⌈4 / α⌉₊ := Nat.le_ceil _
    have h2 : ((⌈4 / α⌉₊ + 1 : ℕ) : ℝ) ≤ n := by
      have hn' : ⌈4 / α⌉₊ + 1 ≤ Fintype.card V := hn
      change ((⌈4 / α⌉₊ + 1 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ)
      exact_mod_cast hn'
    push_cast at h2
    linarith
  have hαn : 4 < α * n := by
    have := (div_lt_iff₀' hα).mp hnα
    linarith
  have hn0 : 0 < n := lt_trans (by positivity) hnα
  have hw1 : 2 + 4 * (α / (8 * M) * n) < α * n := by
    have : 4 * (α / (8 * M) * n) ≤ α * n / 2 := by
      rw [show 4 * (α / (8 * M) * n) = (α * n / 2) / M by field_simp; ring]
      exact div_le_self (by positivity) hM1
    linarith
  have hw2 : 5 * (α / (8 * M) * n) * 2 ^ h.choose 2 < α * n := by
    change 5 * (α / (8 * M) * n) * M < α * n
    have : 5 * (α / (8 * M) * n) * M = 5 / 8 * (α * n) := by field_simp
    rw [this]
    nlinarith
  have heq : lattice (subHost H (edges H \ B)) F =
      SparseEdge.lattice H.G H.lab F ⊓ SparseEdge.zeroOn B :=
    SparseEdge.lattice_sdiff_eq_of_windows h3 h4 B (α / (8 * M) * n) hdeg hw1 hw2
  rw [heq,Submodule.mem_inf]
  rfl

theorem commonNbr_after_edge_payment_explicit (α : ℝ) (hα : 0 < α)
    {V I : Type*} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (B : Finset (Sym2 V)) (d : ℕ) (h3 : CommonNbrCond H F α)
    (hdeg : ∀ v,SparseEdge.degIn B v ≤ d)
    (hsmall : (d : ℝ) ≤ α / 4 * Fintype.card V) :
    CommonNbrCond (subHost H (edges H \ B)) F (α / 2) := by
  apply TypedTriangle.Residual.commonNbrCond_sdiff h3 B d hdeg
  exact_mod_cast (show (4 : ℝ) * d ≤ α * Fintype.card V by nlinarith [hsmall])

theorem hinge_after_edge_payment_explicit (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h)
    {V I : Type*} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (hn : geometryOrder α h ≤ Fintype.card V)
    (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (C : Finset (Sym2 V)) (d : ℕ) (hCE : C ⊆ edges H)
    (hDeg : ∀ v,SparseEdge.degIn C v ≤ d)
    (hd : (d : ℝ) ≤ hingeBudget α h * Fintype.card V) :
    HingeCond (subHost H (edges H \ C)) F
      (S07V49.hingeConstB α 1 h) (2*h-3) := by
  let M : ℝ := 2 ^ (h.choose 2)
  have hM : 1 ≤ M := by dsimp [M]; exact one_le_pow₀ (by norm_num)
  let η : ℝ := hingeBudget α h
  have hη : 0 < η := by dsimp [η,hingeBudget]; positivity
  let n₀ : ℕ := geometryOrder α h
  let n : ℝ := Fintype.card V
  have hnLower : 128*(h+2)*M/α < n := by
    have hc : 128*(h+2)*M/α ≤ (⌈128*(h+2)*M/α⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hn' : (n₀ : ℝ) ≤ n := by
      have hc : (n₀ : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
      simpa only [n] using hc
    dsimp [n₀,geometryOrder] at hn'
    push_cast at hn'
    linarith
  have hnPos : 0 < n := by
    have hlow : 0 ≤ 128*(h+2)*M/α := by positivity
    linarith
  have hlarge : 128*(h+2)*M < α*n := by
    have := (div_lt_iff₀ hα).mp hnLower
    nlinarith
  have hd' : (d : ℝ) ≤ α*n/(64*M) := by
    calc
      (d : ℝ) ≤ α/(64*M)*n := by simpa only [η,hingeBudget,n,M] using hd
      _ = α*n/(64*M) := by ring
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hdn : 64*M*(d : ℝ) ≤ α*n := by
    apply (le_div_iff₀ (by positivity : 0 < 64*M)).mp at hd'
    nlinarith [hd']
  have hw1 : 2 + 4*(d : ℝ) ≤ α*n/8 := by
    have hbase : 32 ≤ α*n := by nlinarith [hlarge,hM]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 64*M-64 by nlinarith [hM])
      (show (0:ℝ) ≤ (d:ℝ) by positivity)]
  have hw2 : (5*(d : ℝ) + h + 1)*2^(h.choose 2) ≤ α*n/8 := by
    change (5*(d : ℝ) + h + 1)*M ≤ α*n/8
    nlinarith [hlarge,hdn]
  exact hinge_after_edge_set_deletion_no_seed H F α h hα hh hH3 hH4 C d
    hCE hDeg (by simpa only [n] using hw1) (by simpa only [n] using hw2)


theorem geometry_after_edge_payment_explicit (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h)
    {V I : Type*} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (B : Finset (Sym2 V)) (d : ℕ)
    (hn : geometryOrder α h ≤ Fintype.card V)
    (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (hBE : B ⊆ edges H) (hDeg : ∀ v,SparseEdge.degIn B v ≤ d)
    (hSmall : (d : ℝ) ≤ geometryBudget α h * Fintype.card V) :
    CommonNbrCond (subHost H (edges H \ B)) F (α/2) ∧
      HingeCond (subHost H (edges H \ B)) F (S07V49.hingeConstB α 1 h) (2*h-3) := by
  have hnReal : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have h3Small : (d : ℝ) ≤ α / 4 * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnReal)
  have h4Small : (d : ℝ) ≤ hingeBudget α h * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hnReal)
  exact ⟨commonNbr_after_edge_payment_explicit α hα H F B d hH3 hDeg h3Small,
    hinge_after_edge_payment_explicit α h hα hh H F hn hH3 hH4 B d hBE hDeg h4Small⟩

#print axioms sparse_edge_deletion_host_explicit
#print axioms commonNbr_after_edge_payment_explicit
#print axioms hinge_after_edge_payment_explicit
#print axioms geometry_after_edge_payment_explicit

end TypedTriangle.Vortex.ExplicitPaid
