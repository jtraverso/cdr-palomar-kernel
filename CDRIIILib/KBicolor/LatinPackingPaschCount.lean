/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.LatinPackingGeometry
public import RequestProject.TypedTriangle.ApplicationsLatinPaschIntercalates
public import RequestProject.TypedTriangle.PaschEmbeddingStatistics

/-! # Pasch configurations in an embedded Latin packing -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical TypedTriangle TypedTriangle.Applications.Latin
variable {k n m : ℕ} {lab : Fin n → Fin k} {X Y : Fin k}
variable {r c s : Fin m → Fin n} (h : LatPlace lab X Y r c s)

def placementMap (r c s : Fin m → Fin n) (p : Fin 3 × Fin m) : Fin n :=
  if p.1=0 then r p.2 else if p.1=1 then c p.2 else s p.2

include h

theorem placementMap_injective : Function.Injective (placementMap r c s) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ he
  fin_cases i <;> fin_cases j <;> simp only [placementMap] at he ⊢ <;>
    norm_num at he ⊢
  · exact h.rinj he
  · exact False.elim (h.rc a b he)
  · exact False.elim (h.rs a b he)
  · exact False.elim (h.rc b a he.symm)
  · exact h.cinj he
  · exact False.elim (h.cs a b he)
  · exact False.elim (h.rs b a he.symm)
  · exact False.elim (h.cs b a he.symm)
  · exact h.sinj he

def placementEmbedding : (Fin 3 × Fin m) ↪ Fin n :=
  ⟨placementMap r c s, placementMap_injective h⟩

theorem map_latinTriangle (i j q : Fin m) :
    (latinTriangle i j q).map (placementEmbedding h) = placedTriangle r c s i j q := by
  simp [latinTriangle, placedTriangle, placementEmbedding, placementMap]

theorem map_decomposition (L : LatinSquare (Fin m)) :
    Pasch.mapConfiguration (placementEmbedding h) (decomposition L) = latPackK r c s L := by
  ext T
  simp only [Pasch.mem_mapConfiguration, decomposition, mem_image, mem_univ, true_and,
    latPackK]
  constructor
  · rintro ⟨U,⟨⟨i,j⟩,rfl⟩,rfl⟩
    exact ⟨(i,j), (map_latinTriangle h i j (L i j)).symm⟩
  · rintro ⟨⟨i,j⟩,rfl⟩
    exact ⟨latinTriangle i j (L i j),⟨(i,j),rfl⟩,map_latinTriangle h i j (L i j)⟩

theorem count_latin_packing (L : LatinSquare (Fin m)) :
    Pasch.count (latPackK r c s L) = (intercalates L).card := by
  rw [← map_decomposition h L, Pasch.count_mapConfiguration]
  convert count_decomposition_eq_intercalates L using 1
  exact congrArg (fun d : DecidableEq (Vertex (Fin m)) =>
    @Pasch.count (Vertex (Fin m)) d (decomposition L)) (Subsingleton.elim _ _)

end CDRBicolour.KBicolor.LatinPasch
