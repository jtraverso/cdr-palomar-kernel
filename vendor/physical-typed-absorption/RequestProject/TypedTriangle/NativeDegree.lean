/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeLinkParts
public import RequestProject.S10.PhysicalAdapter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The triangle degree condition used in S10 follows from original H3,
without assuming a new seed on the core. -/

open Finset Classical
noncomputable section
namespace TypedTriangle
namespace NativeReal
variable {V I : Type*} [Fintype V]

theorem degree_of_H3 {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond (⟨G,lab⟩ : Host V I) F α) :
    S10V22.DegreeCond (S10V22.allowedTri G lab F) (1 / α) := by
  classical
  intro T hT e he
  have hTA := S10V22.mem_allowedTri.mp hT
  induction e using Sym2.ind with
  | _ u v =>
    have he' : u ∈ T ∧ v ∈ T ∧ u ≠ v := by
      simpa [S10V22.edgesOf, and_assoc] using he
    obtain ⟨a, hau, hav, rfl⟩ := ActiveCover.allowed_eq_triple hTA.1 he'.1 he'.2.1 he'.2.2
    have hlink : (linkGraph (⟨G,lab⟩ : Host V I) F u).Adj v a := ⟨hav.symm,hTA⟩
    have hmin := link_minDeg hH3 hlink
    have hcard : (univ.filter ((linkGraph (⟨G,lab⟩ : Host V I) F u).Adj v)).card ≤
        (S10V22.triOn (S10V22.allowedTri G lab F) s(u,v)).card := by
      refine Finset.card_le_card_of_injOn (fun w => ({u,v,w} : Finset V)) ?_ ?_
      · intro w hw
        have hw' := (mem_filter.mp hw).2
        have hne := linkGraph_adj_ne hw'
        apply S10V22.mem_triOn.mpr
        exact ⟨S10V22.mem_allowedTri.mpr hw'.2, by simp [S10V22.edgesOf, hne.1]⟩
      · intro w hw z hz heq
        have hneW := linkGraph_adj_ne (mem_filter.mp hw).2
        have hneZ := linkGraph_adj_ne (mem_filter.mp hz).2
        have hwz : w ∈ ({u,v,z} : Finset V) := by
          change ({u,v,w} : Finset V) = {u,v,z} at heq
          rw [← heq]; simp
        simpa [hneW.2.1.symm, hneW.2.2.symm] using hwz
    have hr : ((univ.filter ((linkGraph (⟨G,lab⟩ : Host V I) F u).Adj v)).card : ℝ) ≤
        (S10V22.triOn (S10V22.allowedTri G lab F) s(u,v)).card := by exact_mod_cast hcard
    simpa [div_div, mul_comm] using hmin.trans hr

end NativeReal
end TypedTriangle
