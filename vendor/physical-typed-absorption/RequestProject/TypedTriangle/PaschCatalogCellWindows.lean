module
public import RequestProject.TypedTriangle.ExplicitBankCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
open CatalogNative.Explicit S07V42.Explicit

def weightedCatalogSupport (α β : ℝ) (h d c E d' c' E' : ℕ) : ℕ :=
  PreparedSupply.Explicit.supplySupport (α/2) h (4*rerouteSize β d c E d' c' E')

/-- The existing catalog parameters already pay the stronger windows in which
the saturated set is avoided on the original carrier. It is not counted in
the bounded local support used by the potential. -/
theorem catalog_cell_weighted_windows {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (h d c E d' c' E' nW n z b : ℕ)
    (hn : catalogCellOrder α β h d c E d' c' E' ≤ nW) (hW : nW ≤ n)
    (hz : (z:ℝ) ≤ catalogCellDeletionBudget α β h*nW)
    (hb : (b:ℝ) ≤ catalogCellDegreeBudget α β h*nW) :
    ((weightedCatalogSupport α β h d c E d' c' E':ℕ):ℝ)+z+3+4*b ≤ α/2*n ∧
    (((weightedCatalogSupport α β h d c E d' c' E':ℕ):ℝ)+z+1+h+5*b)*
      2^h.choose 2 ≤ α/2*n := by
  let k := 4*rerouteSize β d c E d' c' E'
  let Ub := PreparedSupply.Explicit.supplySupport (α/2) h k
  let D : ℝ := 2^h.choose 2
  let Dnext : ℝ := 2^(h+1).choose 2
  have hD1 : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hDn0 : 0 < Dnext := by dsimp [Dnext]; positivity
  have hDD : D ≤ Dnext :=
    pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 (by omega))
  have hWreal : (nW:ℝ) ≤ n := by exact_mod_cast hW
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hnW0 : (0:ℝ) ≤ nW := Nat.cast_nonneg nW
  have hOrder : boundedPieceOrder (α/2) h k ≤ nW := by
    change 2*boundedPieceOrder (α/2) h k+⌈40*(rerouteSize β d c E d' c' E':ℝ)/β⌉₊+1 ≤ nW at hn
    omega
  have hSupply : S07V30.n0 (α/2) Ub h 0 ≤ n := by
    exact ((le_max_right _ _).trans hOrder).trans hW
  let A : ℝ := 8*(((Ub:ℝ)+3)+((Ub:ℝ)+1+h)*D)/(α/2)
  have hA : A < n := by
    have hc := Nat.le_ceil A
    have hh : ((⌈A⌉₊+1+2*0:ℕ):ℝ) ≤ n := by exact_mod_cast hSupply
    push_cast at hh
    linarith only [hc, hh]
  have hConsts : ((Ub:ℝ)+3)+((Ub:ℝ)+1+h)*D < α*n/16 := by
    have hh := (div_lt_iff₀ (show 0 < α/2 by positivity)).mp hA
    nlinarith only [hh]
  have hZδ : (z:ℝ) ≤ ExplicitGeometry.deletionBudget α h*n := by
    have hδ := (ExplicitGeometry.deletionBudget_spec hα h).1.le
    exact (hz.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnW0)).trans
      (mul_le_mul_of_nonneg_left hWreal hδ)
  have hZDnext : (z:ℝ)*Dnext ≤ α*n/4 := by
    have hδ : ExplicitGeometry.deletionBudget α h ≤ α/(4*Dnext) := min_le_right _ _
    calc (z:ℝ)*Dnext ≤ (α/(4*Dnext)*n)*Dnext :=
        mul_le_mul_of_nonneg_right
          (hZδ.trans (mul_le_mul_of_nonneg_right hδ hn0)) hDn0.le
      _ = α*n/4 := by field_simp <;> ring
  have hZD : (z:ℝ)*D ≤ α*n/4 :=
    (mul_le_mul_of_nonneg_left hDD (Nat.cast_nonneg z)).trans hZDnext
  have hbδ : (b:ℝ) ≤ (boundedPieceBudget (α/2) h/2)*n := by
    have hδ := (boundedPieceBudget_pos h (show 0 < α/2 by positivity)).le
    exact (hb.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hnW0)).trans
      (mul_le_mul_of_nonneg_left hWreal (by positivity))
  have hbD : (b:ℝ)*D ≤ α*n/160 := by
    have hδ : boundedPieceBudget (α/2) h ≤ (α/2)/(40*D) := min_le_right _ _
    have hh := div_le_div_of_nonneg_right hδ (by norm_num : (0:ℝ) ≤ 2)
    calc (b:ℝ)*D ≤ (((α/2)/(40*D))/2*n)*D :=
        mul_le_mul_of_nonneg_right
          (hbδ.trans (mul_le_mul_of_nonneg_right hh hn0)) hD0.le
      _ = α*n/160 := by field_simp <;> ring
  have hzD : (z:ℝ) ≤ z*D := le_mul_of_one_le_right (Nat.cast_nonneg z) hD1
  have hbd : (b:ℝ) ≤ b*D := le_mul_of_one_le_right (Nat.cast_nonneg b) hD1
  have hU : (Ub:ℝ)+3 < α*n/16 := by
    have hh : 0 ≤ ((Ub:ℝ)+1+h)*D := by positivity
    linarith only [hConsts, hh]
  have hUD : ((Ub:ℝ)+1+h)*D < α*n/16 := by
    have hh : 0 ≤ (Ub:ℝ)+3 := by positivity
    linarith only [hConsts, hh]
  change (Ub:ℝ)+z+3+4*b ≤ α/2*n ∧ ((Ub:ℝ)+z+1+h+5*b)*D ≤ α/2*n
  constructor
  · nlinarith only [hU, hZD, hbD, hzD, hbd, mul_nonneg hα.le hn0]
  · nlinarith only [hUD, hZD, hbD, mul_nonneg hα.le hn0]

#print axioms catalog_cell_weighted_windows
end TypedTriangle.Pasch
