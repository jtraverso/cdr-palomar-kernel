/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V27.CoreComponent
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Elementary route-contract projection after deleting a small set from a
sampled core. S07V25.S07_core_delete provides a stronger integrated result. -/

open Finset Classical S07V24
noncomputable section

namespace TypedTriangle.Vortex

theorem routeProp_sdiff {V I : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {t : ℕ} {ε : ℝ} {W : Finset V}
    (hε : 0 ≤ ε) (hroute : S07V27.RouteProp G lab F t ε W)
    (A : Finset V) (hA : (A.card : ℝ) ≤ ε/2 * Fintype.card V) :
    S07V27.RouteProp G lab F t (ε/2) (W \ A) := by
  intro Z B _ d hZ hB hd v x y hAdm
  have hZA : ((Z ∪ A).card : ℝ) ≤ ε * Fintype.card V := by
    have hc := Finset.card_union_le Z A
    have hcR : (((Z ∪ A).card : ℝ)) ≤ Z.card + A.card := by exact_mod_cast hc
    nlinarith [hZ,hA]
  have hd' : (d : ℝ) ≤ ε * Fintype.card V := by
    have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
    nlinarith [hd,hε]
  obtain ⟨p,hp,hW,hAvoid,hEdges⟩ := hroute (Z ∪ A) B d hZA hB hd' v x y hAdm
  refine ⟨p,hp,?_,?_,hEdges⟩
  · intro z hz
    rw [mem_intlSet] at hz
    obtain ⟨i, rfl⟩ := hz
    refine mem_sdiff.mpr ⟨hW ((mem_intlSet _ _ _).2 ⟨i, rfl⟩), ?_⟩
    intro hza
    exact hAvoid i (Finset.mem_union_right _ hza)
  · intro i hzi
    exact hAvoid i (Finset.mem_union_left _ hzi)

#print axioms routeProp_sdiff

end TypedTriangle.Vortex
