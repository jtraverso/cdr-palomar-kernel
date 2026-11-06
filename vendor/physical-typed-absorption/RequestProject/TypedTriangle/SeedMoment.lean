/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.LocalizedCoverDown
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.LocalizedCover
variable {V I : Type*} [Fintype V]

/-- Exact fractional edge loads convert every triangular monitor into its edge
pairing on the host. This is an equality, without a sampling or lattice premise. -/
theorem seed_moment_identity {H : Host V I} {F : Set (Multiset I)} {C : ℝ}
    {φ : Finset V → ℝ} (hφ : IsDiffuseSeed H F C φ) (lam : Sym2 V → ℝ) :
    (∑ T ∈ allowed H F, φ T*triSum lam T) = edgeSum lam (edges H) := by
  have hbdry : ∀ e, bdry H F φ e = indR (edges H) e := by
    intro e
    by_cases he : e ∈ edges H
    · simp [indR,he,hφ.bdry_eq_one (mem_filter.mp he).2]
    · simp [indR,he,bdry_eq_zero_of_not_mem H F φ he]
  calc (∑ T ∈ allowed H F, φ T*triSum lam T) =
      ∑ T ∈ allowed H F, ∑ e, lam e*(φ T*indR (triEdges T) e) := by
        apply sum_congr rfl
        intro T _
        rw [triSum,edgeSum_eq_pairing,mul_sum]
        apply sum_congr rfl
        intro e _
        ring
    _ = ∑ e, lam e*bdry H F φ e := by
      rw [sum_comm]
      simp only [bdry,mul_sum]
    _ = ∑ e, lam e*indR (edges H) e := by simp_rw [hbdry]
    _ = edgeSum lam (edges H) := (edgeSum_eq_pairing _ _).symm

/-- A signed triangular quota bounds the moment of the ACTUAL nibble remainder.
The packing may be expressed in the ambient host; containment in the seed host
is checked explicitly, which is useful with a protected basal reserve. -/
theorem remainder_moment_of_quota {H K : Host V I} {F : Set (Multiset I)} {C : ℝ}
    {φ : Finset V → ℝ} (hφ : IsDiffuseSeed H F C φ)
    (P : Finset (Finset V)) (hP : IsPacking K F P)
    (hPE : P.biUnion triEdges ⊆ edges H) (lam : Sym2 V → ℝ) (E0 : ℝ)
    (hquota : |(∑ T ∈ P, triSum lam T)-(∑ T ∈ allowed H F, φ T*triSum lam T)| ≤ E0) :
    |edgeSum lam (edges H\P.biUnion triEdges)| ≤ E0 := by
  have hrem : edgeSum lam (edges H\P.biUnion triEdges) =
      edgeSum lam (edges H)-edgeSum lam (P.biUnion triEdges) := by
    have hh := sum_sdiff hPE (f:=lam)
    dsimp [edgeSum]
    linarith
  rw [hrem,packing_edge_sum_eq hP,←seed_moment_identity hφ]
  simpa only [abs_sub_comm] using hquota

lemma triangle_moment_bound {H : Host V I} {F : Set (Multiset I)} {T : Finset V}
    (hT : IsAllowed H F T) (L : ℝ) (hL : 0 ≤ L) (lam : Sym2 V → ℝ)
    (hlam : ∀ e, |lam e| ≤ L) : |triSum lam T| ≤ 3*L := by
  have hc : (triEdges T).card = 3 := by
    rw [←NativeNibble.nibble_triEdges_eq]
    exact PartitionedTriangleAbsorption.Nibble.card_triEdges hT.1
  calc |triSum lam T| ≤ ∑ e ∈ triEdges T, |lam e| := abs_sum_le_sum_abs _ _
       _ ≤ ∑ _e ∈ triEdges T, L := sum_le_sum fun e _ => hlam e
       _ = 3*L := by simp [hc]
end TypedTriangle.LocalizedCover
