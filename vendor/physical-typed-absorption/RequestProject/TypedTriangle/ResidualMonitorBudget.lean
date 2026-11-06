/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.MonitoredStockTransition
public import RequestProject.S07V44.Uniform
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
open LocalizedCover S07V42 S07V44
variable {V I : Type*} [Fintype V]

lemma pairing_integer_indicator (lam : Sym2 V → ℝ) (S : Finset (Sym2 V)) :
    (∑ e, lam e * ((ind S e : ℤ) : ℝ)) = edgeSum lam S := by
  simp [ind,edgeSum]

/-- The norm of the actual INTEGER monitor is controlled by its representing
edge weights, without replacing the physical quotient by its real span. -/
theorem physical_monitor_norm_of_edge_moments
    {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V}
    {d c E R A M K : ℕ} {C0 : CoreCompression H lab F W d c E}
    {bad : Finset V} (Mon : PhysicalMonitors C0 R bad A M K)
    (x : MCore H lab F W) (J : Finset (Sym2 V))
    (hx : (x : Sym2 V → ℤ) = ind J) (lam : Fin K → Sym2 V → ℝ)
    (hrep : ∀ j, ∑ e, lam j e * ((x.1 e : ℤ) : ℝ) =
      physMonReal C0 (Dset C0 R bad) Mon.psi j x)
    (B : ℝ) (hmom : ∀ j, |edgeSum (lam j) J| ≤ B) :
    (S07V32.l1 (physMon C0 (Dset C0 R bad) Mon.psi x) : ℝ) ≤ K*B := by
  have heach : ∀ j : Fin K,
      |((physMon C0 (Dset C0 R bad) Mon.psi x j : ℤ) : ℝ)| ≤ B := by
    intro j
    rw [←physMonReal_apply,←hrep j]
    simpa only [hx,pairing_integer_indicator] using hmom j
  calc
    (S07V32.l1 (physMon C0 (Dset C0 R bad) Mon.psi x) : ℝ) =
        ∑ j : Fin K, |((physMon C0 (Dset C0 R bad) Mon.psi x j : ℤ) : ℝ)| := by
          simp [S07V32.l1]
    _ ≤ ∑ _j : Fin K, B := sum_le_sum (fun j _ => heach j)
    _ = K*B := by simp

/-- The stock term is paid, not discarded: localized cover-down controls
L-X, and the ACTUAL basal decomposition of X controls its remaining moment.
This derives the integer monitor bound for the real leftover L from the
nibble quota on U and the two degree budgets. Core-profile membership is an
intermediate input to be obtained for that same sampled core. -/
theorem stock_residual_integer_monitor_bound
    (H : Host V I) (F : Set (Multiset I)) (D : Finset (Finset V))
    (hD : IsDecomposition H F (BasalIncidence.cover D) D)
    (J : Finset (Sym2 V)) {W : Finset V} {d c E R A M K : ℕ}
    {C0 : CoreCompression H.G H.lab F W d c E} {bad : Finset V}
    (Mon : PhysicalMonitors C0 R bad A M K) (x : MCore H.G H.lab F W)
    (hx : (x : Sym2 V → ℤ) = ind J)
    (lam : Fin K → Sym2 V → ℝ)
    (hrep : ∀ j, ∑ e, lam j e * ((x.1 e : ℤ) : ℝ) =
      physMonReal C0 (Dset C0 R bad) Mon.psi j x)
    (L DX DC E0 : ℝ) (hL : 0 ≤ L)
    (hstock : ∀ v, (((BasalIncidence.cover D).filter (fun e => v ∈ e)).card : ℝ) ≤ DX)
    (htri : ∀ j T, IsAllowed H F T → |triSum (lam j) T| ≤ 3*L*(T∩bad).card)
    (hleft : ∀ j, |edgeSum (lam j) J-edgeSum (lam j) (BasalIncidence.cover D)| ≤
      E0+(3*L*bad.card)*DC/2) :
    (S07V32.l1 (physMon C0 (Dset C0 R bad) Mon.psi x) : ℝ) ≤
      K*(E0+(3*L*bad.card)*(DC+DX)/2) := by
  have hstock' : ∀ j, |edgeSum (lam j) (BasalIncidence.cover D)| ≤
      (3*L*bad.card)*DX/2 := by
    intro j
    have hb := packing_localized_bound (show IsPacking H F D from ⟨hD.1,hD.2.1⟩)
      DX L hL (by simpa only [hD.2.2] using hstock) bad (lam j) (htri j)
    rw [←packing_edge_sum_eq (show IsPacking H F D from ⟨hD.1,hD.2.1⟩),hD.2.2] at hb
    exact hb
  apply physical_monitor_norm_of_edge_moments Mon x J hx lam hrep
  intro j
  have hh := abs_add_le (edgeSum (lam j) J-edgeSum (lam j) (BasalIncidence.cover D))
    (edgeSum (lam j) (BasalIncidence.cover D))
  have hh' := hh.trans (add_le_add (hleft j) (hstock' j))
  simpa only [sub_add_cancel] using (show
    |edgeSum (lam j) J-edgeSum (lam j) (BasalIncidence.cover D)+
      edgeSum (lam j) (BasalIncidence.cover D)| ≤
      E0+(3*L*bad.card)*(DC+DX)/2 by nlinarith only [hh'])

end TypedTriangle.CatalogNative
