/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexCleanHinge
public import RequestProject.TypedTriangle.VortexNestedH4Transport
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex

private theorem card_clean_hinges_pull {X Y I : Type*} [Fintype X] [Fintype Y]
    (ι : Y → X) (hι : Function.Injective ι) (hSurj : Function.Surjective ι)
    (G : SimpleGraph X) (lab : X → I) (F : Set (Multiset I))
    (u v a b : Y) (i : ℕ) :
    ((SparseEdge.hinges G lab F (ι u) (ι v) (ι a) (ι b) i).filter
      (fun J => s(ι a,ι b) ∉ J)).card ≤
    ((SparseEdge.hinges (G.comap ι) (lab ∘ ι) F u v a b i).filter
      (fun J => s(a,b) ∉ J)).card := by
  have hRange : ∀ x, (∃ y, ι y = x) ↔ x ∉ (∅ : Finset X) := by
    intro x
    exact ⟨fun _ => by simp,fun _ => hSurj x⟩
  rw [← Finset.card_map (Finset.mapEmbedding (S07V42.emb2 hι)).toEmbedding]
  apply Finset.card_le_card
  intro J hJ
  obtain ⟨hMember,hClean⟩ := mem_filter.mp hJ
  obtain ⟨J',rfl⟩ := S07V42.hinge_edges_from hι hRange
    (show S07V24.freeV (ι u) (ι v) (ι a) (ι b) J ⊆ univ \ (∅ : Finset X) by simp)
  have hParts := (mem_filter.mp hMember).2
  have hPull : J' ∈ SparseEdge.hinges (G.comap ι) (lab ∘ ι) F u v a b i := by
    refine mem_filter.mpr ⟨mem_univ _,S07V42.isHinge_pull hι hParts.1,?_⟩
    rw [← hParts.2,S07V42.support_map hι,Finset.card_map]
  refine mem_map.mpr ⟨J',mem_filter.mpr ⟨hPull,?_⟩,rfl⟩
  intro hBad
  exact hClean (mem_map.mpr ⟨s(a,b),hBad,by
    simp only [S07V42.emb2_apply,Sym2.map_mk]⟩)

/-- Clean hinges transport between the actual direct and nested vertex
carriers without changing their density or order. -/
theorem cleanHingeCond_equiv {V W I : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (H₁ : Host V I) (H₂ : Host W I)
    (F : Set (Multiset I)) (α : ℝ) (h : ℕ)
    (hAdj : ∀ x y, H₁.G.Adj x y ↔ H₂.G.Adj (e x) (e y))
    (hLab : ∀ x, H₁.lab x = H₂.lab (e x))
    (hClean : CleanHingeCond H₁ F α h) : CleanHingeCond H₂ F α h := by
  let ι : W → V := e.symm
  have hι : Function.Injective ι := e.symm.injective
  have hG : H₂.G = H₁.G.comap ι := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    change H₂.G.Adj x y ↔ H₁.G.Adj (ι x) (ι y)
    simpa only [ι,e.apply_symm_apply] using (hAdj (e.symm x) (e.symm y)).symm
  have hL : H₂.lab = H₁.lab ∘ ι := by
    funext x
    simpa only [Function.comp_apply,ι,e.apply_symm_apply] using (hLab (e.symm x)).symm
  have hHost : H₂ = (⟨H₁.G.comap ι,H₁.lab ∘ ι⟩ : Host W I) :=
    congrArg₂ (fun G lab => (⟨G,lab⟩ : Host W I)) hG hL
  rw [hHost]
  intro u v a b hab hTa hTb
  have hTa' : IsAllowed H₁ F {ι u,ι v,ι a} := by
    have hh := (S07V42.isAllowed_comap_iff hι (G := H₁.G)
      (lab := H₁.lab) (F := F) ({u,v,a} : Finset W)).mp hTa
    simpa only [← S07V42.triple_map hι,IsAllowed,SparseEdge.IsAllowed] using hh
  have hTb' : IsAllowed H₁ F {ι u,ι v,ι b} := by
    have hh := (S07V42.isAllowed_comap_iff hι (G := H₁.G)
      (lab := H₁.lab) (F := F) ({u,v,b} : Finset W)).mp hTb
    simpa only [← S07V42.triple_map hι,IsAllowed,SparseEdge.IsAllowed] using hh
  obtain ⟨i,hi6,hih,hCount⟩ := hClean (ι u) (ι v) (ι a) (ι b)
    (fun he => hab (hι he)) hTa' hTb'
  refine ⟨i,hi6,hih,?_⟩
  have hCard : Fintype.card V = Fintype.card W := Fintype.card_congr e
  rw [← hCard]
  exact hCount.trans (by exact_mod_cast
    card_clean_hinges_pull ι hι e.symm.surjective H₁.G H₁.lab F u v a b i)

#print axioms cleanHingeCond_equiv
end TypedTriangle.Vortex
