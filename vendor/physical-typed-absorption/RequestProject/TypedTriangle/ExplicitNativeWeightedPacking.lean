/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitDiffuseWeightedPacking
public import RequestProject.TypedTriangle.NativeWeightedPacking
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.NativeNibble.Explicit
open PartitionedTriangleAbsorption

def nativePackingCut (C c η : ℝ) (q : ℕ) : ℕ :=
  max 1 ⌈WeightedClone.Explicit.cloneCut C c η (Pseudorandom.Explicit.egjCut (1/4) 4) q⌉₊

theorem weighted_packing_of_diffuse_seed_explicit (C c η : ℝ) (q : ℕ)
    (hC : 0 < C) (hc : 0 < c) (hη : 0 < η) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), nativePackingCut C c η q ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      ∀ (κ : Type) [Fintype κ] (W : κ → Finset V → ℝ),
      (Fintype.card κ:ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → 0 ≤ W k T ∧ W k T ≤ 1) →
      (∀ k, c*Fintype.card V ≤ ∑ T ∈ allowed H F, φ T*W k T) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ TypedTriangle.IsPacking H F P ∧
        ∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed H F, φ T*W k T)| ≤
          η*(∑ T ∈ allowed H F, φ T*W k T) := by
  let n₀ := WeightedClone.Explicit.cloneCut C c η (Pseudorandom.Explicit.egjCut (1/4) 4) q
  have hMatch := WeightedClone.Explicit.diffuse_weighted_matching_explicit C c η q hC hc hη
  intro V I _ H F φ hn hφ κ _ W hκ hW hmass
  classical
  have hn1 : 1 ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnpos : (0:ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hn₀ : n₀ ≤ (Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  let P := fun i => triEdges ((system H F).tri i)
  let ψ := weights H F φ
  have hallowed i := isAllowed_of_mem_allowed (system_mem H F i)
  have hE : (Fintype.card (Sym2 V):ℝ) ≤ (Fintype.card V:ℝ)^2 := by
    have hh := Fintype.card_le_of_surjective (Sym2.mk (α:=V)).uncurry Sym2.mk_surjective
    have hh' : Fintype.card (Sym2 V) ≤ (Fintype.card V)^2 := by simpa [pow_two] using hh
    exact_mod_cast hh'
  have hcard : ∀ i, (P i).card = 3 := by
    intro i
    change (triEdges ((system H F).tri i)).card = 3
    rw [←nibble_triEdges_eq]
    exact Nibble.card_triEdges ((system H F).card_tri i)
  have hψ : ∀ i, 1/(C*Fintype.card V) ≤ ψ i ∧ ψ i ≤ C/Fintype.card V :=
    fun i => hφ.1 _ (hallowed i)
  have hload : ∀ e, ∑ i, (if e ∈ P i then ψ i else 0) ≤ 1 := by
    intro e
    have heq : (∑ i, if e ∈ P i then ψ i else 0) = (system H F).load ψ e := by
      simp only [Nibble.TriSystem.load,Nibble.TriSystem.edgeTris,sum_filter,nibble_triEdges_eq,P]
    rw [heq,system_load]
    by_cases he : e ∈ H.G.edgeSet
    · exact le_of_eq (hφ.2 e he)
    · apply le_trans (b := 0)
      · apply le_of_eq
        apply sum_eq_zero
        intro T hT
        obtain ⟨hT,heT⟩ := mem_filter.mp hT
        have heH := triEdges_subset_edges (isAllowed_of_mem_allowed hT) heT
        exact False.elim (he (by simpa only [edges,mem_filter,mem_univ,true_and] using heH))
      · norm_num
  have hlinear : ∀ e f, e ≠ f → (univ.filter fun i => e ∈ P i ∧ f ∈ P i).card ≤ 1 := by
    intro e f hef
    simpa only [Nibble.TriSystem.edgeTris,filter_filter,nibble_triEdges_eq,P] using
      (system H F).edgeTris_inter_card_le hef
  have hsumAll (k : κ) : (∑ i, ψ i*W k ((system H F).tri i)) =
      ∑ T ∈ allowed H F, φ T*W k T := system_sum H F (fun T => φ T*W k T)
  obtain ⟨Q,hQ,hWeights⟩ := hMatch (Fintype.card V) hn₀ (Sym2 V) (Fin (allowed H F).card) κ
    P ψ (fun k i => W k ((system H F).tri i)) hE hcard hψ (by
      intro e
      convert hload e using 1
      apply sum_congr rfl
      intro i _
      split_ifs <;> rfl) (by
      intro e f hef
      convert hlinear e f hef using 1
      congr 1
      ext i
      simp only [mem_filter,mem_univ,true_and]) hκ
    (fun k i => hW k _ (hallowed i)) (fun k => by rw [hsumAll]; exact hmass k)
  have hp : Nibble.IsPacking (system H F) Q := by
    intro i hi j hj hij
    simpa only [nibble_triEdges_eq] using hQ hi hj hij
  refine ⟨packed H F Q,?_,packed_isPacking H F Q hp,?_⟩
  · intro T hT
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hT
    exact system_mem H F i
  · intro k
    have hs : (∑ T ∈ packed H F Q, W k T) = ∑ i ∈ Q, W k ((system H F).tri i) := by
      rw [packed,sum_image]
      exact fun _ _ _ _ h => (system H F).tri_inj h
    rw [hs]
    exact (by simpa only [hsumAll] using hWeights k)
#print axioms weighted_packing_of_diffuse_seed_explicit
end TypedTriangle.NativeNibble.Explicit
