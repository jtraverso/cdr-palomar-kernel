/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4SelectorSameResidue
public import RequestProject.TypedTriangle.PositiveModeMoments
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The stock moment is paid when the actual post-cover-down residue enters
the positive selector. The same estimate works for localized and full tests. -/

open Finset Classical
noncomputable section
namespace TypedTriangle.StockEntry
open BasalIncidence LocalizedCover
variable {V I : Type*} [Fintype V]

theorem g4_actual_positive_moment_budget (H : Host V I) (F : Set (Multiset I))
    (D : Finset (Finset V)) (hD : IsDecomposition H F (cover D) D)
    (R J Ps Y : Finset (Sym2 V))
    (hRJ : Disjoint R J) (hPY : Disjoint Ps Y) (hEq : R∪J=Ps∪Y)
    (hR : Basal H F R) (hPs : Basal H F Ps)
    (DX DR DJ DC E0 L : ℝ) (hL : 0 ≤ L)
    (hstock : ∀ v, ((cover D).filter (fun e => v ∈ e)).card ≤ DX)
    (hRd : ∀ v, ((R.filter (fun e => v ∈ e)).card:ℝ) ≤ DR)
    (hJd : ∀ v, ((J.filter (fun e => v ∈ e)).card:ℝ) ≤ DJ)
    (bad : Finset V) (lam : Sym2 V → ℝ)
    (htri : ∀ T, IsAllowed H F T → |triSum lam T| ≤ 3*L*(T∩bad).card)
    (hrel : |edgeSum lam J-edgeSum lam (cover D)| ≤
      E0+(3*L*bad.card)*DC/2) :
    |edgeSum lam Y| ≤ E0+(3*L*bad.card)*(DC+DX+2*DR+DJ)/2 := by
  have hStockMom : |edgeSum lam (cover D)| ≤ (3*L*bad.card)*DX/2 := by
    exact basal_localized_moment ⟨D,hD⟩ DX L hL hstock bad lam htri
  have hJMom : |edgeSum lam J| ≤ E0+(3*L*bad.card)*(DC+DX)/2 := by
    have hh := abs_add_le (edgeSum lam J-edgeSum lam (cover D))
      (edgeSum lam (cover D))
    have hh' := hh.trans (add_le_add hrel hStockMom)
    simpa only [sub_add_cancel] using (show
      |edgeSum lam J-edgeSum lam (cover D)+edgeSum lam (cover D)| ≤
        E0+(3*L*bad.card)*(DC+DX)/2 by nlinarith only [hh'])
  have hModeMom := positive_mode_moment_difference R J Ps Y hRJ hPY hEq hR hPs
    DR DJ L hL hRd hJd bad lam htri
  have hh := abs_add_le (edgeSum lam J) (edgeSum lam Y-edgeSum lam J)
  have hh' := hh.trans (add_le_add hJMom hModeMom)
  have hFinal :
    |edgeSum lam J+(edgeSum lam Y-edgeSum lam J)| ≤
      E0+(3*L*bad.card)*(DC+DX+2*DR+DJ)/2 := by nlinarith only [hh']
  have hEq : edgeSum lam J+(edgeSum lam Y-edgeSum lam J)=edgeSum lam Y := by ring
  rwa [hEq] at hFinal

end TypedTriangle.StockEntry
