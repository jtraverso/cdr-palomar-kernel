/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SeedMoment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.LocalizedCover
variable {V I : Type*} [Fintype V]

theorem seed_total_mass_identity {H : Host V I} {F : Set (Multiset I)} {C : ℝ}
    {φ : Finset V → ℝ} (hφ : IsDiffuseSeed H F C φ) :
    3*(∑ T ∈ allowed H F, φ T) = ((edges H).card:ℝ) := by
  have htri : ∀ T ∈ allowed H F, triSum (fun _ => (1:ℝ)) T = 3 := by
    intro T hT
    have hc : (triEdges T).card = 3 := by
      rw [←NativeNibble.nibble_triEdges_eq]
      exact PartitionedTriangleAbsorption.Nibble.card_triEdges (isAllowed_of_mem_allowed hT).1
    simp [triSum,edgeSum,hc]
  have hh := seed_moment_identity hφ (fun _ => (1:ℝ))
  have hleft : (∑ T ∈ allowed H F, φ T*triSum (fun _ => (1:ℝ)) T) =
      3*(∑ T ∈ allowed H F, φ T) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro T hT
    rw [htri T hT]
    ring
  rw [hleft] at hh
  simpa [edgeSum] using hh

/-- Native mass bound for converting signed packing errors to tau*n^2. -/
theorem seed_total_mass_cap {H : Host V I} {F : Set (Multiset I)} {C : ℝ}
    {φ : Finset V → ℝ} (hφ : IsDiffuseSeed H F C φ) :
    0 ≤ (∑ T ∈ allowed H F, φ T) ∧ (∑ T ∈ allowed H F, φ T) ≤ (Fintype.card V:ℝ)^2 := by
  have hh := seed_total_mass_identity hφ
  have he : ((edges H).card:ℝ) ≤ (Fintype.card V:ℝ)^2 := by
    have hsym := Fintype.card_le_of_surjective (Sym2.mk (α:=V)).uncurry Sym2.mk_surjective
    have hs : Fintype.card (Sym2 V) ≤ (Fintype.card V)^2 := by simpa [pow_two] using hsym
    have hnat : (edges H).card ≤ (Fintype.card V)^2 := (card_le_univ _).trans hs
    exact_mod_cast hnat
  have he0 : (0:ℝ) ≤ (edges H).card := by positivity
  constructor <;> nlinarith [sq_nonneg (Fintype.card V:ℝ)]
end TypedTriangle.LocalizedCover
