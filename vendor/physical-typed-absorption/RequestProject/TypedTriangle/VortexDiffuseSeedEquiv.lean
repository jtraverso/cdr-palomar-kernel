/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexNestedH4Transport
public import RequestProject.TypedTriangle.VortexPhysicalEmbedding
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex

/-- Literal pullback of triangle weights through a vertex equivalence. -/
def equivSeed {V W : Type} (e : V ≃ W) (ψ : Finset W → ℝ) (T : Finset V) : ℝ :=
  ψ (T.map e.toEmbedding)

theorem bdry_equivSeed {V W I : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (H₁ : Host V I) (H₂ : Host W I) (F : Set (Multiset I))
    (hAdj : ∀ u v, H₁.G.Adj u v ↔ H₂.G.Adj (e u) (e v))
    (hLab : ∀ u, H₁.lab u = H₂.lab (e u)) (ψ : Finset W → ℝ) (f : Sym2 V) :
    bdry H₁ F (equivSeed e ψ) f = bdry H₂ F ψ (Sym2.map e f) := by
  have hAdjInv : ∀ u v, H₂.G.Adj u v ↔ H₁.G.Adj (e.symm u) (e.symm v) := by
    intro u v
    simpa only [e.apply_symm_apply] using (hAdj (e.symm u) (e.symm v)).symm
  have hLabInv : ∀ u, H₂.lab u = H₁.lab (e.symm u) := by
    intro u
    simpa only [e.apply_symm_apply] using (hLab (e.symm u)).symm
  unfold bdry
  refine Finset.sum_bij (fun T _ => T.map e.toEmbedding) ?_ ?_ ?_ ?_
  · intro T hT
    exact mem_filter.mpr ⟨mem_univ _,isAllowed_map_equiv e H₁ H₂ F hAdj hLab T
      (isAllowed_of_mem_allowed hT)⟩
  · intro T _ U _ hTU
    exact Finset.map_injective e.toEmbedding hTU
  · intro U hU
    let T := U.map e.symm.toEmbedding
    have hT : IsAllowed H₁ F T := isAllowed_map_equiv e.symm H₂ H₁ F hAdjInv hLabInv U
      (isAllowed_of_mem_allowed hU)
    have hBack : T.map e.toEmbedding = U := by
      dsimp only [T]
      rw [Finset.map_map]
      have hId : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl W := by
        ext x
        exact e.apply_symm_apply x
      rw [hId]
      simp
    exact ⟨T,mem_filter.mpr ⟨mem_univ _,hT⟩,hBack⟩
  · intro T _
    have hMem : Sym2.map e f ∈ triEdges (T.map e.toEmbedding) ↔ f ∈ triEdges T := by
      rw [triEdges_embedding]
      constructor
      · intro hf
        obtain ⟨g,hg,hgf⟩ := mem_image.mp hf
        exact (Sym2.map.injective e.injective hgf) ▸ hg
      · intro hf
        exact mem_image.mpr ⟨f,hf,rfl⟩
    simp only [equivSeed,indR,hMem]

/-- Exact diffuse H1 is invariant under the actual host equivalence; the
same coefficient constant and literal pulled weights are retained. -/
theorem diffuse_seed_pull_equiv {V W I : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (H₁ : Host V I) (H₂ : Host W I) (F : Set (Multiset I)) (C : ℝ)
    (hAdj : ∀ u v, H₁.G.Adj u v ↔ H₂.G.Adj (e u) (e v))
    (hLab : ∀ u, H₁.lab u = H₂.lab (e u)) (ψ : Finset W → ℝ)
    (hψ : IsDiffuseSeed H₂ F C ψ) : IsDiffuseSeed H₁ F C (equivSeed e ψ) := by
  have hCard : Fintype.card V = Fintype.card W := Fintype.card_congr e
  constructor
  · intro T hT
    have hWeights := hψ.1 (T.map e.toEmbedding) (isAllowed_map_equiv e H₁ H₂ F hAdj hLab T hT)
    simpa only [equivSeed,hCard] using hWeights
  · intro f hf
    have hMap : Sym2.map e f ∈ H₂.G.edgeSet := by
      induction f using Sym2.ind with
      | _ u v =>
        rw [Sym2.map_mk]
        exact (SimpleGraph.mem_edgeSet H₂.G).mpr
          ((hAdj u v).mp ((SimpleGraph.mem_edgeSet H₁.G).mp hf))
    change (∑ T ∈ triOn H₁ F f, equivSeed e ψ T) = 1
    rw [← bdry_eq_sum_triOn,bdry_equivSeed e H₁ H₂ F hAdj hLab]
    exact hψ.bdry_eq_one hMap

#print axioms bdry_equivSeed
#print axioms diffuse_seed_pull_equiv
end TypedTriangle.Vortex
