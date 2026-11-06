/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.UniformCompression
public import RequestProject.TypedTriangle.QuotientBox
public import RequestProject.TypedTriangle.QuotientGroup

@[expose] public section

/-!
# Physical instantiation of the finite-box quotient bounds

Local proof candidate, NOT kernel-checked in this campaign.
The hypotheses of the final endpoint are exactly the original H3 and H4.
-/

open Finset
noncomputable section
open Classical

namespace TypedTriangle
open Incidence

variable {V I : Type*} [Fintype V]

/-- Every signed physical triangle boundary is in the physical lattice. -/
theorem triBd_mem_lattice (H : Host V I) (F : Set (Multiset I)) (c : Finset V → ℤ) :
    triBd H F c ∈ lattice H F := by
  change (∑ T ∈ allowed H F, c T • ind (triEdges T)) ∈ lattice H F
  refine Submodule.sum_mem _ fun T hT => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨T, (Finset.mem_filter.1 hT).2, rfl⟩

/-- Instantiate QuotientBox on the actual local group and physical lattice. -/
theorem physQuot_bounds_of_compression (H : Host V I) (F : Set (Multiset I))
    {s H₀ D₀ : ℕ} (cmp : Compression H F s H₀ D₀) :
    Module.finrank ℤ (physQuot H F) ≤ (s + 1) ^ 2 ∧
      Nat.card (Submodule.torsion ℤ (physQuot H F)) ≤
        QuotientBox.torBound ((s + 1) ^ 2) (3 * D₀) := by
  have hdm := card_sym2_le cmp.W cmp.card_W
  apply QuotientBox.quotient_bounds_of_compression ((s + 1) ^ 2) (3 * D₀)
    (localGroup H F) (lattice H F)
    ((fun T => ind (triEdges T)) '' {T | IsAllowed H F T}) rfl
    (lattice_le_localGroup H F) (triBd H F) (triBd_mem_lattice H F)
    cmp.C₀ cmp.P cmp.decomp (eProj cmp.W hdm) (eEmb cmp.W hdm)
    (fun x => eEmb_eProj cmp.W hdm (cmp.supp x))
  rintro g ⟨T, hT, rfl⟩ hg j
  refine (abs_eProj_le cmp.W hdm _ j).trans ?_
  have hb := cmp.costP ⟨ind (triEdges T), hg⟩
  change l1E (cmp.P ⟨ind (triEdges T), hg⟩) ≤
    (D₀ : ℤ) * l1E (ind (triEdges T)) at hb
  rw [l1E_ind_triEdges hT.1] at hb
  push_cast
  linarith

end TypedTriangle

namespace TypedTriangle

/-- Host-independent rank and torsion bounds, derived from H3--H4 alone. -/
theorem physQuot_bounds_of_H3H4 (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ d T n₀ : ℕ, 1 ≤ T ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        Module.finrank ℤ (physQuot H F) ≤ d ∧
          Nat.card (Submodule.torsion ℤ (physQuot H F)) ≤ T := by
  obtain ⟨s, H₀, D₀, n₀, hcmp⟩ := compression_of_H3H4 α h hα
  refine ⟨(s + 1) ^ 2, max 1 (QuotientBox.torBound ((s + 1) ^ 2) (3 * D₀)),
    n₀, le_max_left _ _, fun {V I} _ H F hn hH3 hH4 => ?_⟩
  obtain ⟨cmp⟩ := hcmp H F hn hH3 hH4
  obtain ⟨hrank, htor⟩ := physQuot_bounds_of_compression H F cmp
  exact ⟨hrank, htor.trans (le_max_right _ _)⟩

end TypedTriangle
