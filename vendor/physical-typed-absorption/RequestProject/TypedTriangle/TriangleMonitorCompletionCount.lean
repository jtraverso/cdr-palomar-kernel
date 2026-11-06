/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.LinkRobust
public import RequestProject.TypedTriangle.RobustHinge
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.TriangleMonitors
variable {V I : Type*} [Fintype V]

/-- Removing a literal subfamily of blocks gives a decomposition of the
corresponding edge complement. This supplies the basal remainder for gluing. -/
theorem decomposition_sdiff_of_subfamily {H : Host V I} {F : Set (Multiset I)}
    {J : Finset (Sym2 V)} {D P : Finset (Finset V)}
    (hD : IsDecomposition H F J D) (hPD : P ⊆ D) :
    IsDecomposition H F (J\P.biUnion triEdges) (D\P) := by
  refine ⟨fun T hT => hD.1 T (mem_sdiff.mp hT).1,
    fun T hT S hS hne => hD.2.1 (mem_sdiff.mp hT).1 (mem_sdiff.mp hS).1 hne,?_⟩
  ext e
  constructor
  · intro he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    obtain ⟨hTD,hTP⟩ := mem_sdiff.mp hT
    refine mem_sdiff.mpr ⟨hD.subset hTD heT,?_⟩
    intro heP
    obtain ⟨S,hSP,heS⟩ := mem_biUnion.mp heP
    have hEq : T=S := hD.unique hTD (hPD hSP) heT heS
    exact hTP (hEq ▸ hSP)
  · intro he
    obtain ⟨heJ,heP⟩ := mem_sdiff.mp he
    obtain ⟨T,hTD,heT⟩ := hD.exists_mem heJ
    have hTP : T ∉ P := fun hT => heP (mem_biUnion.mpr ⟨T,hT,heT⟩)
    exact mem_biUnion.mpr ⟨T,mem_sdiff.mpr ⟨hTD,hTP⟩,heT⟩

/-- Retaining the initial packing pays for all subsequent layers at once.
Every added block consumes three previously uncovered edges. -/
theorem completion_card_identity {H : Host V I} {F : Set (Multiset I)}
    {D P : Finset (Finset V)} (hD : IsDecomposition H F (edges H) D)
    (hPD : P ⊆ D) :
    3*(D\P).card = (edges H\P.biUnion triEdges).card := by
  have hP : IsPacking H F P := ⟨fun T hT => hD.1 T (hPD hT),
    fun T hT S hS hne => hD.2.1 (hPD hT) (hPD hS) hne⟩
  have hPE : P.biUnion triEdges ⊆ edges H := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  rw [card_sdiff_of_subset hPD,card_sdiff_of_subset hPE]
  have hcD := decomp_card hD
  have hcP := decomp_card hP.isDecomposition
  omega

/-- A maximum-degree bound for the entire original nibble complement bounds
all blocks subsequently added, including cover-down and absorption. -/
theorem completion_card_le_of_sparse_complement {H : Host V I}
    {F : Set (Multiset I)} {D P : Finset (Finset V)}
    (hD : IsDecomposition H F (edges H) D) (hPD : P ⊆ D) (δ : ℝ)
    (hdeg : ∀ x, (degIn (edges H\P.biUnion triEdges) x:ℝ) ≤ δ*Fintype.card V) :
    ((D\P).card:ℝ) ≤ δ*(Fintype.card V:ℝ)^2/3 := by
  have hi := completion_card_identity hD hPD
  have he : ((edges H\P.biUnion triEdges).card:ℝ) ≤ δ*(Fintype.card V:ℝ)^2 := by
    have h₁ : ((edges H\P.biUnion triEdges).card:ℝ) ≤
        ∑ x : V, (degIn (edges H\P.biUnion triEdges) x:ℝ) := by
      exact_mod_cast card_le_sum_degIn (edges H\P.biUnion triEdges)
    have h₂ := sum_le_sum (fun x (_ : x ∈ (univ : Finset V)) => hdeg x)
    have hsum : (∑ _x : V, δ*(Fintype.card V:ℝ)) = δ*(Fintype.card V:ℝ)^2 := by
      simp [pow_two]; ring
    exact h₁.trans (hsum ▸ h₂)
  have hiR : 3*((D\P).card:ℝ) = ((edges H\P.biUnion triEdges).card:ℝ) := by
    exact_mod_cast hi
  linarith

/-- Signed bounded statistics change by at most the number of added blocks.
The target may be any real number; the application uses the original seed mass. -/
theorem statistic_error_of_extension {D P : Finset (Finset V)} (hPD : P ⊆ D)
    (w : Finset V → ℝ) (hw : ∀ T ∈ D, |w T| ≤ 1) (target error : ℝ)
    (hQuota : |(∑ T ∈ P, w T)-target| ≤ error) :
    |(∑ T ∈ D, w T)-target| ≤ error+(D\P).card := by
  have hsplit := sum_sdiff hPD (f := w)
  have htail : |∑ T ∈ D\P, w T| ≤ ((D\P).card:ℝ) := by
    calc |∑ T ∈ D\P, w T| ≤ ∑ T ∈ D\P, |w T| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _T ∈ D\P, (1:ℝ) := sum_le_sum fun T hT => hw T (mem_sdiff.mp hT).1
      _ = _ := by simp
  have heq : (∑ T ∈ D, w T)-target =
      ((∑ T ∈ P, w T)-target)+(∑ T ∈ D\P, w T) := by linarith
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith only [hQuota,htail])

/-- The final monitor estimate is independent of the number of vortex layers. -/
theorem completed_statistic_error {H : Host V I} {F : Set (Multiset I)}
    {D P : Finset (Finset V)} (hD : IsDecomposition H F (edges H) D)
    (hPD : P ⊆ D) (δ : ℝ)
    (hdeg : ∀ x, (degIn (edges H\P.biUnion triEdges) x:ℝ) ≤ δ*Fintype.card V)
    (w : Finset V → ℝ) (hw : ∀ T, IsAllowed H F T → |w T| ≤ 1)
    (target τ : ℝ) (hQuota : |(∑ T ∈ P, w T)-target| ≤ τ*(Fintype.card V:ℝ)^2) :
    |(∑ T ∈ D, w T)-target| ≤ (τ+δ/3)*(Fintype.card V:ℝ)^2 := by
  have hs := statistic_error_of_extension hPD w (fun T hT => hw T (hD.1 T hT))
    target (τ*(Fintype.card V:ℝ)^2) hQuota
  have hc := completion_card_le_of_sparse_complement hD hPD δ hdeg
  nlinarith only [hs,hc]

#print axioms decomposition_sdiff_of_subfamily
#print axioms completion_card_identity
#print axioms completion_card_le_of_sparse_complement
#print axioms statistic_error_of_extension
#print axioms completed_statistic_error
end TypedTriangle.TriangleMonitors
