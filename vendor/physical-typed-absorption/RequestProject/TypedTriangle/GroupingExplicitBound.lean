/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.GroupingAtomKernelLift
public import RequestProject.TypedTriangle.GroupingKernelExplicitBound
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Submodule Classical
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace TypedTriangle.Grouping
open QuotientBox

/-- The numerical bound uses only arithmetic recursion on dimension. -/
def explicitGroupBound (d B R : ℕ) : ℕ :=
  GroupingExplicit.kernelBound d (max B R)

noncomputable section

theorem minimal_charge_le_explicit {d B R : ℕ}
    (S : Finset (Fin d → ℤ)) (hS : S ⊆ box d R) (m : Alph d B → ℕ)
    (hm : Minimal (IsZeroSum (span ℤ (S : Set (Fin d → ℤ)))) m) :
    (∑ a, m a) ≤ explicitGroupBound d B R := by
  obtain ⟨u,hproj,hu,hzero,hmin,hMass⟩ := exists_irreducible_atom_lift S m hm
  exact hMass.trans (GroupingExplicit.kernel_atom_bound d (max B R)
    (atomLiftColumns d B S) u (atomLift_columns_bounded S hS) hu hzero hmin)

theorem atomBound_le_explicit {d B R : ℕ}
    (S : Finset (Fin d → ℤ)) (hS : S ⊆ box d R) :
    atomBound d B (span ℤ (S : Set (Fin d → ℤ))) ≤ explicitGroupBound d B R := by
  unfold atomBound
  apply Finset.sup_le
  intro m hm
  exact minimal_charge_le_explicit S hS m
    ((minimal_finite d B (span ℤ (S : Set (Fin d → ℤ)))).mem_toFinset.mp hm)

/-- A genuine explicit majorant of the original Dickson-based constant.
The integer lattice and all mathematical hypotheses remain unchanged. -/
theorem groupBound_le_explicit (d B R : ℕ) :
    groupBound d B R ≤ explicitGroupBound d B R := by
  unfold groupBound
  apply max_le
  · have hpos := GroupingExplicit.kernelBound_pos d (max B R)
    exact hpos
  · apply Finset.sup_le
    intro S hS
    exact atomBound_le_explicit S (mem_powerset.mp hS)

/-- The actual grouping consumer with a numerical constant fixed before
the lattice, the token family and its multiplicities. -/
theorem uniform_grouping_numerical {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d B R : ℕ) (Γ : Submodule ℤ (Fin d → ℤ)) (G : Set (Fin d → ℤ))
    (hΓ : Γ = span ℤ G) (hG : ∀ g ∈ G, ∀ k, |g k| ≤ R)
    (z : ι → Fin d → ℤ) (hz : ∀ i k, |z i k| ≤ B) (hsum : ∑ i, z i ∈ Γ) :
    ∃ P : Finpartition (univ : Finset ι),
      ∀ J ∈ P.parts, J.card ≤ explicitGroupBound d B R ∧ ∑ i ∈ J, z i ∈ Γ := by
  obtain ⟨P,hP⟩ := uniform_grouping d B R Γ G hΓ hG z hz hsum
  exact ⟨P,fun J hJ => ⟨(hP J hJ).1.trans (groupBound_le_explicit d B R),
    (hP J hJ).2⟩⟩

#print axioms minimal_charge_le_explicit
#print axioms atomBound_le_explicit
#print axioms groupBound_le_explicit
#print axioms uniform_grouping_numerical
end
end TypedTriangle.Grouping
