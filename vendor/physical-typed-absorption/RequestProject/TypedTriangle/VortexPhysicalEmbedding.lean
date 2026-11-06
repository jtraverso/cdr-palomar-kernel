/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexEmbeddedPaidAssembly
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex

/-- Zero extension of integer edge coordinates through an injective vertex map. -/
def edgeVectorPush {V W : Type} (ι : V ↪ W) :
    (Sym2 V → ℤ) →ₗ[ℤ] (Sym2 W → ℤ) where
  toFun x e := if he : ∃ f, Sym2.map ι f = e then x (Classical.choose he) else 0
  map_add' x y := by funext e; dsimp; split_ifs <;> simp
  map_smul' r x := by funext e; dsimp; split_ifs <;> simp

theorem edgeVectorPush_apply_map {V W : Type} (ι : V ↪ W)
    (x : Sym2 V → ℤ) (f : Sym2 V) :
    edgeVectorPush ι x (Sym2.map ι f) = x f := by
  change (if he : ∃ g, Sym2.map ι g = Sym2.map ι f then x (Classical.choose he) else 0) = _
  split_ifs with he
  · have hEq : Classical.choose he = f :=
      (Sym2.map.injective ι.injective) (Classical.choose_spec he)
    exact congrArg x hEq
  · exact False.elim (he ⟨f,rfl⟩)

theorem edgeVectorPush_ind {V W : Type} (ι : V ↪ W) (E : Finset (Sym2 V)) :
    edgeVectorPush ι (ind E) = ind (embeddedEdges ι E) := by
  funext e
  by_cases he : ∃ f, Sym2.map ι f = e
  · obtain ⟨f,rfl⟩ := he
    rw [edgeVectorPush_apply_map]
    have hMem : Sym2.map ι f ∈ embeddedEdges ι E ↔ f ∈ E := by
      constructor
      · intro hf
        obtain ⟨g,hg,hgf⟩ := mem_image.mp hf
        exact (Sym2.map.injective ι.injective hgf) ▸ hg
      · intro hf
        exact mem_image.mpr ⟨f,hf,rfl⟩
    simp only [ind,hMem]
  · have hNot : e ∉ embeddedEdges ι E := by
      intro hE
      obtain ⟨f,hf,hfe⟩ := mem_image.mp hE
      exact he ⟨f,hfe⟩
    change (if hh : ∃ f, Sym2.map ι f = e then ind E (Classical.choose hh) else 0) = _
    simp only [dif_neg he,ind,if_neg hNot]

/-- Physicality pushes through a graph embedding into its actual target
host. The target host is not assumed to be physical. -/
theorem physical_embedding {V W I : Type} [Fintype V] [Fintype W]
    (J : Host V I) (H : Host W I) (F : Set (Multiset I)) (ι : V ↪ W)
    (hAdj : ∀ u v, J.G.Adj u v → H.G.Adj (ι u) (ι v))
    (hLab : ∀ u, J.lab u = H.lab (ι u)) {E : Finset (Sym2 V)}
    (hE : IsPhysical J F E) : IsPhysical H F (embeddedEdges ι E) := by
  have hPush : ∀ x ∈ lattice J F, edgeVectorPush ι x ∈ lattice H F := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨T,hT,rfl⟩ := hx
      have hBasal : Basal J F (triEdges T) := by
        refine ⟨{T},?_,?_,?_⟩
        · intro U hU
          obtain rfl := mem_singleton.mp hU
          exact hT
        · simp
        · simp
      obtain ⟨D,hD⟩ := basal_embedding J H F ι hAdj hLab hBasal
      rw [edgeVectorPush_ind]
      exact isPhysical_of_isDecomposition hD
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul r x hx ih => rw [map_smul]; exact Submodule.smul_mem _ r ih
  have hResult := hPush (ind E) hE
  rw [edgeVectorPush_ind] at hResult
  exact hResult

#print axioms physical_embedding
end TypedTriangle.Vortex
