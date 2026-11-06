/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.LocalizedCoverDown
public import RequestProject.TypedTriangle.CorePositiveRefiner
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.LocalizedCover
variable {V I : Type*} [Fintype V]

theorem basal_localized_moment {H : Host V I} {F : Set (Multiset I)}
    {R : Finset (Sym2 V)} (hR : Basal H F R)
    (D L : ℝ) (hL : 0 ≤ L)
    (hdeg : ∀ v, ((R.filter (fun e => v ∈ e)).card:ℝ) ≤ D)
    (bad : Finset V) (lam : Sym2 V → ℝ)
    (htri : ∀ T, IsAllowed H F T → |triSum lam T| ≤ 3*L*(T∩bad).card) :
    |edgeSum lam R| ≤ (3*L*bad.card)*D/2 := by
  obtain ⟨DD,hDD⟩ := hR
  have hPack : IsPacking H F DD := ⟨hDD.1,hDD.2.1⟩
  rw [←hDD.2.2,packing_edge_sum_eq hPack]
  exact packing_localized_bound hPack D L hL (by simpa only [hDD.2.2] using hdeg) bad lam htri

/-- The positive withdrawal changes a localized moment by the cost of BOTH
basal modes. The removed mode is bounded by its inclusion in R union J.
No assumption places the entire initial stock inside the child core. -/
theorem positive_mode_moment_difference {H : Host V I} {F : Set (Multiset I)}
    (R J P Y : Finset (Sym2 V)) (hRJ : Disjoint R J) (hPY : Disjoint P Y)
    (hEq : R∪J = P∪Y) (hR : Basal H F R) (hP : Basal H F P)
    (DR DJ L : ℝ) (hL : 0 ≤ L)
    (hRd : ∀ v, ((R.filter (fun e => v ∈ e)).card:ℝ) ≤ DR)
    (hJd : ∀ v, ((J.filter (fun e => v ∈ e)).card:ℝ) ≤ DJ)
    (bad : Finset V) (lam : Sym2 V → ℝ)
    (htri : ∀ T, IsAllowed H F T → |triSum lam T| ≤ 3*L*(T∩bad).card) :
    |edgeSum lam Y-edgeSum lam J| ≤ (3*L*bad.card)*(2*DR+DJ)/2 := by
  have hSub : P ⊆ R∪J := by rw [hEq]; exact subset_union_left
  have hPd : ∀ v, ((P.filter (fun e => v ∈ e)).card:ℝ) ≤ DR+DJ := by
    intro v
    have h1 := card_le_card (filter_subset_filter (p:=fun e => v ∈ e) hSub)
    have h2 := card_union_le (R.filter (fun e => v ∈ e)) (J.filter (fun e => v ∈ e))
    rw [filter_union] at h1
    have h3 : ((P.filter (fun e => v ∈ e)).card:ℝ) ≤
      ((R.filter (fun e => v ∈ e)).card:ℝ)+(J.filter (fun e => v ∈ e)).card := by
      exact_mod_cast h1.trans h2
    linarith [hRd v,hJd v]
  have hRmom := basal_localized_moment hR DR L hL hRd bad lam htri
  have hPmom := basal_localized_moment hP (DR+DJ) L hL hPd bad lam htri
  have hSum : edgeSum lam R+edgeSum lam J = edgeSum lam P+edgeSum lam Y := by
    have hh := congrArg (edgeSum lam) hEq
    simpa only [edgeSum,sum_union hRJ,sum_union hPY] using hh
  have hDiff : edgeSum lam Y-edgeSum lam J = edgeSum lam R-edgeSum lam P := by
    linarith only [hSum]
  rw [hDiff]
  have hh := abs_add_le (edgeSum lam R) (-(edgeSum lam P))
  simp only [abs_neg,←sub_eq_add_neg] at hh
  exact (hh.trans (add_le_add hRmom hPmom)).trans_eq (by ring)

end TypedTriangle.LocalizedCover
