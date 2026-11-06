/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexNestedH3Transfer
public import RequestProject.S07V42.DeletionGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

/-- A permitted physical triangle remains permitted under an exact
vertex relabelling of the host. -/
theorem isAllowed_map_equiv {V W I : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (H₁ : Host V I) (H₂ : Host W I)
    (F : Set (Multiset I))
    (hAdj : ∀ x y, H₁.G.Adj x y ↔ H₂.G.Adj (e x) (e y))
    (hLab : ∀ x, H₁.lab x = H₂.lab (e x))
    (T : Finset V) (hT : IsAllowed H₁ F T) :
    IsAllowed H₂ F (T.map e.toEmbedding) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Finset.card_map] using hT.1
  · intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hy
    have hab : a ≠ b := by
      intro he
      exact hxy (congrArg e he)
    exact (hAdj a b).1 (hT.2.1 a ha b hb hab)
  · have hLabel : (T.map e.toEmbedding).val.map H₂.lab =
        T.val.map H₁.lab := by
      rw [Finset.map_val, Multiset.map_map]
      congr 1
      funext x
      exact (hLab x).symm
    rw [hLabel]
    exact hT.2.2

/-- The three edge coordinates of a triangle are preserved by vertex
relabelling. -/
theorem mem_triEdges_map_equiv {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (T : Finset V) (f : Sym2 V) :
    Sym2.map e f ∈ triEdges (T.map e.toEmbedding) ↔ f ∈ triEdges T := by
  induction f using Sym2.ind with
  | _ x y =>
    rw [Sym2.map_mk, mem_triEdges, mem_triEdges]
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨⟨a,ha,hax⟩,⟨b,hb,hby⟩,hxy⟩
      have hax' : a = x := e.injective hax
      have hby' : b = y := e.injective hby
      exact ⟨hax' ▸ ha,hby' ▸ hb,fun h => hxy (congrArg e h)⟩
    · rintro ⟨hx,hy,hxy⟩
      exact ⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩,fun h => hxy (e.injective h)⟩

theorem triEdges_map_equiv {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (T : Finset V) :
    triEdges (T.map e.toEmbedding) = (triEdges T).image (Sym2.map e) := by
  ext f
  constructor
  · intro hf
    let g := Sym2.map e.symm f
    have hmap : Sym2.map e g = f := by
      induction f using Sym2.ind with
      | _ x y => simp [g]
    exact Finset.mem_image.mpr ⟨g,(mem_triEdges_map_equiv e T g).1
      (by simpa only [hmap] using hf),hmap⟩
  · intro hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    exact (mem_triEdges_map_equiv e T g).2 hg

/-- A physical decomposition is invariant under an exact relabelling. -/
theorem isDecomposition_map_equiv {V W I : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (H₁ : Host V I) (H₂ : Host W I)
    (F : Set (Multiset I))
    (hAdj : ∀ x y, H₁.G.Adj x y ↔ H₂.G.Adj (e x) (e y))
    (hLab : ∀ x, H₁.lab x = H₂.lab (e x))
    (J : Finset (Sym2 V)) (D : Finset (Finset V))
    (hD : IsDecomposition H₁ F J D) :
    IsDecomposition H₂ F (J.image (Sym2.map e))
      (D.image (fun T => T.map e.toEmbedding)) := by
  refine ⟨?_,?_,?_⟩
  · intro T hT
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
    exact isAllowed_map_equiv e H₁ H₂ F hAdj hLab S (hD.1 S hS)
  · intro T hT U hU hne
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hU
    have hSR : S ≠ R := by
      intro h
      exact hne (congrArg (fun Z : Finset V => Z.map e.toEmbedding) h)
    change Disjoint (triEdges (S.map e.toEmbedding))
      (triEdges (R.map e.toEmbedding))
    rw [triEdges_map_equiv, triEdges_map_equiv,
      Finset.disjoint_image (Sym2.map.injective e.injective)]
    exact hD.2.1 hS hR hSR
  · ext f
    rw [← hD.2.2]
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨S,⟨T,hT,rfl⟩,hf⟩
      rw [triEdges_map_equiv] at hf
      obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
      exact ⟨g,⟨T,hT,hg⟩,rfl⟩
    · rintro ⟨g,⟨T,hT,hg⟩,rfl⟩
      exact ⟨T.map e.toEmbedding,⟨T,hT,rfl⟩,
        by rw [triEdges_map_equiv]; exact Finset.mem_image.mpr ⟨g,hg,rfl⟩⟩

/-- Exact H4 transport along the canonical change of the sampled subtype.
The counting inequality is the no-deletion specialization of the physical
hinge pull-back construction. -/
theorem hingeCond_equiv {V W I : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (H₁ : Host V I) (H₂ : Host W I)
    (F : Set (Multiset I)) (α : ℝ) (h : ℕ)
    (hAdj : ∀ x y, H₁.G.Adj x y ↔ H₂.G.Adj (e x) (e y))
    (hLab : ∀ x, H₁.lab x = H₂.lab (e x))
    (h4 : HingeCond H₁ F α h) : HingeCond H₂ F α h := by
  let ι : W → V := e.symm
  have hι : Function.Injective ι := e.symm.injective
  have hG : H₂.G = H₁.G.comap ι := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    change H₂.G.Adj x y ↔ H₁.G.Adj (ι x) (ι y)
    simpa only [ι, e.apply_symm_apply] using (hAdj (e.symm x) (e.symm y)).symm
  have hL : H₂.lab = H₁.lab ∘ ι := by
    funext x
    change H₂.lab x = H₁.lab (ι x)
    simpa only [ι, e.apply_symm_apply] using (hLab (e.symm x)).symm
  change SparseEdge.HingeCond H₂.G H₂.lab F α h
  rw [hG, hL]
  intro u v a b hab hua hub
  have hrange (x : V) : (∃ y : W, ι y = x) ↔ x ∉ (∅ : Finset V) := by
    constructor
    · intro _; simp
    · intro _; exact ⟨e x,e.symm_apply_apply x⟩
  have hua' : SparseEdge.IsAllowed H₁.G H₁.lab F {ι u,ι v,ι a} := by
    have hh := (S07V42.isAllowed_comap_iff hι (G := H₁.G)
      (lab := H₁.lab) (F := F) ({u,v,a} : Finset W)).1 hua
    simpa only [← S07V42.triple_map hι] using hh
  have hub' : SparseEdge.IsAllowed H₁.G H₁.lab F {ι u,ι v,ι b} := by
    have hh := (S07V42.isAllowed_comap_iff hι (G := H₁.G)
      (lab := H₁.lab) (F := F) ({u,v,b} : Finset W)).1 hub
    simpa only [← S07V42.triple_map hι] using hh
  have hab' : ι a ≠ ι b := fun hh => hab (hι hh)
  have h4' : SparseEdge.HingeCond H₁.G H₁.lab F α h := h4
  obtain ⟨i,hi6,hih,hcount⟩ := h4' (ι u) (ι v) (ι a) (ι b) hab' hua' hub'
  refine ⟨i,hi6,hih,?_⟩
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e
  rw [← hcard]
  have hpull := S07V42.card_hinges_pull_ge hι hrange
    (G := H₁.G) (lab := H₁.lab) (F := F) u v a b i
  have hfilter :
      (SparseEdge.hinges H₁.G H₁.lab F (ι u) (ι v) (ι a) (ι b) i).filter
        (fun J => S07V24.freeV (ι u) (ι v) (ι a) (ι b) J ⊆ univ \ (∅ : Finset V)) =
      SparseEdge.hinges H₁.G H₁.lab F (ι u) (ι v) (ι a) (ι b) i := by
    simp
  rw [hfilter] at hpull
  exact hcount.trans (by exact_mod_cast hpull)

/-- H4 on the prepared nested subtype is H4 on the same direct sampled
window used by the resource bank. No density or constant is lost. -/
theorem nested_prepared_hingeCond_direct {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    (A : Finset (Survivors (univ \ W))) (α : ℝ) (h : ℕ)
    (h4 : HingeCond
      (restrictedHost (restrictedHost H (univ \ W)) A) F α h) :
    SparseEdge.HingeCond
      (H.G.comap (Subtype.val : {v : V // v ∈ W \ liftVertexSet (univ \ W) A} → V))
      (H.lab ∘ Subtype.val) F α h := by
  let e := nestedToDirectWindowEquiv W A
  let H' : Host {v : V // v ∈ W \ liftVertexSet (univ \ W) A} I :=
    ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  have hh : HingeCond H' F α h :=
    hingeCond_equiv e (restrictedHost (restrictedHost H (univ \ W)) A)
      H' F α h (fun _ _ => Iff.rfl) (fun _ => rfl) h4
  exact hh

#print axioms isAllowed_map_equiv
#print axioms mem_triEdges_map_equiv
#print axioms triEdges_map_equiv
#print axioms isDecomposition_map_equiv
#print axioms hingeCond_equiv
#print axioms nested_prepared_hingeCond_direct

end TypedTriangle.Vortex
