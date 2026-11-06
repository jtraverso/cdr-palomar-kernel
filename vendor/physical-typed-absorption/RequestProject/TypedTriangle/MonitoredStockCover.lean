/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.MonitoredCoverDown
public import RequestProject.TypedTriangle.BasalStockEntry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.StockEntry
open BasalIncidence LocalizedCover
variable {V I : Type*} [Fintype V]

/-- The original stock completion window suffices for all localized monitors
simultaneously. A separately protected bank costs no extra candidate loss when
both the stock and the uncovered edges are already disjoint from it. -/
theorem stock_cover_down_monitored {H : Host V I} {F : Set (Multiset I)}
    {D : Finset (Finset V)} {κ : ℝ}
    (hD : IsDecomposition H F (cover D) D)
    (hSupply : ∀ u v, H.G.Adj u v → κ*Fintype.card V ≤ (good H F D u v).card)
    (U : Finset (Sym2 V)) (hUH : U ⊆ edges H) (hUX : Disjoint U (cover D))
    (hUphys : IsPhysical H F U) {d q : ℕ}
    (hdeg : ∀ v, (U.filter (fun e => v ∈ e)).card ≤ d)
    (hwin : ((U.card+q*(2*d+4*q):ℕ):ℝ) < q*κ*Fintype.card V) :
    ∃ P : Finset (Finset V), IsPacking H F P ∧ U ⊆ P.biUnion triEdges ∧
      P.biUnion triEdges ⊆ U∪cover D ∧
      (∀ v, ((P.biUnion triEdges).filter (fun e => v ∈ e)).card ≤ 2*d+2*q) ∧
      IsPhysical H F (cover D\P.biUnion triEdges) ∧
      ∀ (lam : Sym2 V → ℝ) (bad : Finset V) (L E0 : ℝ), 0 ≤ L →
        (∀ T, IsAllowed H F T → |triSum lam T| ≤ 3*L*(T∩bad).card) →
        |edgeSum lam U| ≤ E0 →
        |edgeSum lam (cover D\P.biUnion triEdges)-edgeSum lam (cover D)| ≤
          E0+(3*L*bad.card)*(2*d+2*q:ℕ)/2 := by
  have hdiag : ∀ e ∈ U, ¬e.IsDiag := by
    intro e he
    exact H.G.not_isDiag_of_mem_edgeSet (by simpa [edges] using hUH he)
  have hcand : ∀ e ∈ U,
      U.card+q*(2*d+4*q+2*0) < q*(candidates H F (cover D) e).card := by
    intro e he
    have hmass : κ*Fintype.card V ≤ (candidates H F (cover D) e).card := by
      induction e using Sym2.ind with
      | h u v =>
        have huv : H.G.Adj u v := by simpa [edges] using hUH he
        exact (hSupply u v huv).trans (by exact_mod_cast card_le_card (good_subset_candidates H F D u v))
    have hh := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg q : (0:ℝ) ≤ q)
    have hh' : ((U.card+q*(2*d+4*q+2*0):ℕ):ℝ) <
        (q:ℝ)*(candidates H F (cover D) e).card := by push_cast; push_cast at hwin; nlinarith
    exact_mod_cast hh'
  obtain ⟨P,hP,hCov,hSub,_,hDeg,hPhys,hMom⟩ := physical_monitored_cover_down H F U (cover D) ∅
    hUX (by simp) hdiag hUphys (isPhysical_of_isDecomposition hD)
    (candidates H F (cover D)) (fun e _ w hw => (mem_filter.mp hw).2)
    hdeg (fun _ => by simp) hcand
  exact ⟨P,hP,hCov,hSub,hDeg,hPhys,hMom⟩
end TypedTriangle.StockEntry
