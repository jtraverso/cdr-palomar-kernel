/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.PhysicalQuotientBounds
public import RequestProject.TypedTriangle.PhysicalGrouping
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)

@[expose] public section

/-! Local physical instantiation of V14. Candidate pending the rc3 integration audit.
Constants are chosen before the host. The cells may be signed and need only lie
in the local group individually; their total is required to be physically integral. -/

open Finset Classical

noncomputable section

namespace TypedTriangle

open Incidence

variable {V I : Type*} [Fintype V]

theorem physical_token_grouping_of_compression (H : Host V I) (F : Set (Multiset I))
    {s H₀ D₀ : ℕ} (cmp : Compression H F s H₀ D₀) (k : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → localGroup H F)
    (hb : ∀ i, l1E (b i : Sym2 V → ℤ) ≤ k)
    (hsum : ∑ i, (b i : Sym2 V → ℤ) ∈ lattice H F) :
    ∃ Q : Finpartition (Finset.univ : Finset ι),
      ∀ J ∈ Q.parts, J.card ≤ Grouping.groupBound ((s + 1) ^ 2) (D₀ * k) (3 * D₀) ∧
        ∑ i ∈ J, (b i : Sym2 V → ℤ) ∈ lattice H F := by
  have hdm := card_sym2_le cmp.W cmp.card_W
  have hbox : ∀ g ∈ ((fun T => ind (triEdges T)) '' {T | IsAllowed H F T}),
      ∀ hg : g ∈ localGroup H F, ∀ j,
        |eProj cmp.W hdm (cmp.P ⟨g, hg⟩) j| ≤ ((3 * D₀ : ℕ) : ℤ) := by
    rintro g ⟨T, hT, rfl⟩ hg j
    refine (abs_eProj_le cmp.W hdm _ j).trans ?_
    have hcost := cmp.costP ⟨ind (triEdges T), hg⟩
    change l1E (cmp.P ⟨ind (triEdges T), hg⟩) ≤ (D₀ : ℤ) * l1E (ind (triEdges T)) at hcost
    rw [l1E_ind_triEdges hT.1] at hcost
    push_cast
    linarith
  have htokens : ∀ i j,
      |eProj cmp.W hdm (cmp.P (b i)) j| ≤ ((D₀ * k : ℕ) : ℤ) := by
    intro i j
    refine (abs_eProj_le cmp.W hdm _ j).trans ?_
    have hcost := cmp.costP (b i)
    have hsmall := hb i
    push_cast
    exact hcost.trans (mul_le_mul_of_nonneg_left hsmall (by positivity))
  exact (Grouping.physical_grouping_of_compression ((s + 1) ^ 2) (D₀ * k) (3 * D₀)
    (localGroup H F) (lattice H F)
    ((fun T => ind (triEdges T)) '' {T | IsAllowed H F T}) rfl
    (lattice_le_localGroup H F) (triBd H F) (triBd_mem_lattice H F)
    cmp.C₀ cmp.P cmp.decomp (eProj cmp.W hdm) (eEmb cmp.W hdm)
    (fun x => eEmb_eProj cmp.W hdm (cmp.supp x)) hbox b htokens hsum).2

/-- Physical grouping from the original H3--H4, with no compression provider premise. -/
theorem physical_token_grouping_of_H3H4 (α : ℝ) (h k : ℕ) (hα : 0 < α) :
    ∃ N n₀ : ℕ, 1 ≤ N ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → localGroup H F),
          (∀ i, l1E (b i : Sym2 V → ℤ) ≤ k) →
          (∑ i, (b i : Sym2 V → ℤ) ∈ lattice H F) →
          ∃ Q : Finpartition (Finset.univ : Finset ι),
            ∀ J ∈ Q.parts, J.card ≤ N ∧ ∑ i ∈ J, (b i : Sym2 V → ℤ) ∈ lattice H F := by
  obtain ⟨s, H₀, D₀, n₀, hcmp⟩ := compression_of_H3H4 α h hα
  refine ⟨Grouping.groupBound ((s + 1) ^ 2) (D₀ * k) (3 * D₀), n₀,
    Grouping.one_le_groupBound _ _ _, ?_⟩
  intro V I _ H F hn hH3 hH4 ι _ _ b hb hsum
  obtain ⟨cmp⟩ := hcmp H F hn hH3 hH4
  exact physical_token_grouping_of_compression H F cmp k b hb hsum

end TypedTriangle
