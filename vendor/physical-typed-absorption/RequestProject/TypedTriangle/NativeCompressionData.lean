/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.PhysicalTokenGrouping
public import RequestProject.TypedTriangle.PreparedComposition
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)

@[expose] public section

/-! Native compression data for the V16 composition. Candidate pending rc3.
The local-profile module maps to the actual local group, never to its saturation.
-/

open Finset Classical
noncomputable section

namespace TypedTriangle

open Incidence

variable {V I : Type*} [Fintype V]

def nativeLocalProfile (H : Host V I) (F : Set (Multiset I)) :
    Composition.localProfile H.G H.lab F →ₗ[ℤ] localGroup H F where
  toFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma native_compression_decomp (H : Host V I) (F : Set (Multiset I))
    {s H₀ D₀ : ℕ} (cmp : Compression H F s H₀ D₀)
    (x : Composition.localProfile H.G H.lab F) :
    (x : Sym2 V → ℤ) - (cmp.P.comp (nativeLocalProfile H F)) x =
      triBd H F ((cmp.C₀.comp (nativeLocalProfile H F)) x) :=
  cmp.decomp (nativeLocalProfile H F x)

/-- Actual compression supplies both coordinate bounds required in V16.
The tile norm threshold is arbitrary, fixed before the host in applications. -/
theorem native_compression_coordinates (H : Host V I) (F : Set (Multiset I))
    {s H₀ D₀ : ℕ} (cmp : Compression H F s H₀ D₀) (k : ℕ) :
    ∃ coord : (Sym2 V → ℤ) →ₗ[ℤ] (Fin ((s + 1) ^ 2) → ℤ),
    ∃ emb : (Fin ((s + 1) ^ 2) → ℤ) →ₗ[ℤ] (Sym2 V → ℤ),
      (∀ x, emb (coord ((cmp.P.comp (nativeLocalProfile H F)) x)) =
        (cmp.P.comp (nativeLocalProfile H F)) x) ∧
      (∀ g ∈ Composition.latGens H.G H.lab F,
        ∀ hg : g ∈ Composition.localProfile H.G H.lab F, ∀ j,
          |coord ((cmp.P.comp (nativeLocalProfile H F)) ⟨g, hg⟩) j| ≤ (3 * D₀ : ℕ)) ∧
      (∀ b : Composition.localProfile H.G H.lab F,
        Dispersal.l1E (b : Sym2 V → ℤ) ≤ k → ∀ j,
          |coord ((cmp.P.comp (nativeLocalProfile H F)) b) j| ≤ (D₀ * k : ℕ)) := by
  have hdm := card_sym2_le cmp.W cmp.card_W
  refine ⟨eProj cmp.W hdm, eEmb cmp.W hdm, ?_, ?_, ?_⟩
  · intro x
    exact eEmb_eProj cmp.W hdm (cmp.supp (nativeLocalProfile H F x))
  · rintro g ⟨T, hT, rfl⟩ hg j
    refine (abs_eProj_le cmp.W hdm _ j).trans ?_
    have hc := cmp.costP (nativeLocalProfile H F ⟨ind (triEdges T), hg⟩)
    change l1E (cmp.P (nativeLocalProfile H F ⟨ind (triEdges T), hg⟩)) ≤
      (D₀ : ℤ) * l1E (ind (triEdges T)) at hc
    rw [l1E_ind_triEdges hT.1] at hc
    change l1E (cmp.P (nativeLocalProfile H F ⟨ind (triEdges T), hg⟩)) ≤ (3 * D₀ : ℕ)
    push_cast
    linarith
  · intro b hb j
    refine (abs_eProj_le cmp.W hdm _ j).trans ?_
    have hc := cmp.costP (nativeLocalProfile H F b)
    push_cast
    exact hc.trans (mul_le_mul_of_nonneg_left hb (by positivity))

end TypedTriangle
