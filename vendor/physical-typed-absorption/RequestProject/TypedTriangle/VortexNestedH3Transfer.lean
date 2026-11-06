/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexSubtypeLift
public import RequestProject.TypedTriangle.SparseEdgeDefs
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

/-- H3 is invariant under a relabelling that preserves the host graph and
part labels. This is the geometric part of the nested-survivor bridge. -/
theorem commonNbrCond_equiv {V W I : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (H₁ : Host V I) (H₂ : Host W I) (F : Set (Multiset I))
    (α : ℝ)
    (hAdj : ∀ x y, H₁.G.Adj x y ↔ H₂.G.Adj (e x) (e y))
    (hLab : ∀ x, H₁.lab x = H₂.lab (e x))
    (h3 : CommonNbrCond H₁ F α) : CommonNbrCond H₂ F α := by
  intro u v huv k hk
  have heq (u v : W) :
      (commonNbrs H₂ k u v).card =
        (commonNbrs H₁ k (e.symm u) (e.symm v)).card := by
    refine Finset.card_bij (fun x _ => e.symm x) ?_ ?_ ?_
    · intro x hx
      simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨hux,hvx,hlx⟩ := hx
      refine ⟨?_,?_,?_⟩
      · have hu : H₂.G.Adj (e (e.symm u)) (e (e.symm x)) := by simpa using hux
        exact (hAdj (e.symm u) (e.symm x)).2 hu
      · have hv : H₂.G.Adj (e (e.symm v)) (e (e.symm x)) := by simpa using hvx
        exact (hAdj (e.symm v) (e.symm x)).2 hv
      · have hl : H₁.lab (e.symm x) = H₂.lab x := by simpa using hLab (e.symm x)
        exact hl.trans hlx
    · intro x _ y _ hxy
      exact e.symm.injective hxy
    · intro x hx
      refine ⟨e x, ?_, e.symm_apply_apply x⟩
      simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨hux,hvx,hlx⟩ := hx
      refine ⟨?_,?_,?_⟩
      · simpa using (hAdj (e.symm u) x).1 hux
      · simpa using (hAdj (e.symm v) x).1 hvx
      · exact (hLab x).symm.trans hlx
  have hne : e.symm u ≠ e.symm v := by
    intro he
    exact huv (e.symm.injective he)
  have htype : ({H₁.lab (e.symm u), H₁.lab (e.symm v), k} : Multiset I) ∈ F := by
    simpa [hLab (e.symm u), hLab (e.symm v)] using hk
  have hh := h3 (e.symm u) (e.symm v) hne k htype
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e
  rw [heq]
  simpa [hcard] using hh

/-- The two subtype presentations of a prepared sampled window carry the
same underlying vertices. -/
def nestedToDirectWindowEquiv {V : Type*} [Fintype V]
    (W : Finset V) (A : Finset (Survivors (univ \ W))) :
    Survivors A ≃ {v : V // v ∈ W \ liftVertexSet (univ \ W) A} where
  toFun x := ⟨x.1.1, by
    have hxW : x.1.1 ∈ W := by
      by_contra hn
      exact x.1.2 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩)
    have hxA : x.1.1 ∉ liftVertexSet (univ \ W) A := by
      intro h
      exact x.2 ((mem_liftVertexSet (univ \ W) A x.1).mp h)
    exact Finset.mem_sdiff.mpr ⟨hxW,hxA⟩⟩
  invFun y := by
    have hyW := (Finset.mem_sdiff.mp y.2).1
    have hyA := (Finset.mem_sdiff.mp y.2).2
    let x : Survivors (univ \ W) := ⟨y.1, by
      intro h
      exact (Finset.mem_sdiff.mp h).2 hyW⟩
    exact ⟨x,by
      intro h
      exact hyA ((mem_liftVertexSet (univ \ W) A x).mpr h)⟩
  left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro y; apply Subtype.ext; rfl

/-- H3 on the prepared nested subtype is H3 on the direct membership subtype
used by the G3 bank. -/
theorem nested_prepared_commonNbrCond_direct {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    (A : Finset (Survivors (univ \ W))) (α : ℝ)
    (h3 : CommonNbrCond
      (restrictedHost (restrictedHost H (univ \ W)) A) F α) :
    SparseEdge.CommonNbrCond
      (H.G.comap (Subtype.val : {v : V // v ∈ W \ liftVertexSet (univ \ W) A} → V))
      (H.lab ∘ Subtype.val) F α := by
  let e := nestedToDirectWindowEquiv W A
  let H' : Host {v : V // v ∈ W \ liftVertexSet (univ \ W) A} I :=
    ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  have hh : CommonNbrCond H' F α :=
    commonNbrCond_equiv e (restrictedHost (restrictedHost H (univ \ W)) A)
      H' F α (fun _ _ => Iff.rfl) (fun _ => rfl) h3
  exact hh

#print axioms commonNbrCond_equiv
#print axioms nested_prepared_commonNbrCond_direct

end TypedTriangle.Vortex
