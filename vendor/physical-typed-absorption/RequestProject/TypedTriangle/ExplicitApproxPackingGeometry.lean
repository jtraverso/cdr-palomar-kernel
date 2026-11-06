/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import PartitionedTriangleAbsorption.Nibble.Iterate
public import RequestProject.TypedTriangle.SeedCaps
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
namespace PartitionedTriangleAbsorption.Nibble.TriSystem
variable {V : Type} [Fintype V] [DecidableEq V] {m : ℕ} (S : TriSystem V m)

/-- An ordinary triangle system has at most one triangle for each third vertex
through a prescribed edge. No positive lower bound on triangle weights is used. -/
theorem edgeTris_card_le_vertices (e : Sym2 V) :
    (S.edgeTris e).card ≤ Fintype.card V := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst y
      have he : S.edgeTris s(x,x) = ∅ := by
        ext i
        simp [mem_edgeTris, mem_triEdges]
      simp [he]
    have hz : ∀ i : ↥(S.edgeTris s(x,y)), ∃ z : V,
        z ∈ S.tri i ∧ z ≠ x ∧ z ≠ y := by
      intro i
      have hnot : ¬ S.tri i ⊆ {x,y} := by
        intro hsub
        have hc := card_le_card hsub
        rw [S.card_tri, card_pair hxy] at hc
        omega
      obtain ⟨z,hz,hzpair⟩ := Finset.not_subset.mp hnot
      refine ⟨z,hz,?_⟩
      simpa only [mem_insert, mem_singleton, not_or] using hzpair
    choose f hf using hz
    have hfInj : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      apply S.tri_inj
      have hi := (mem_triEdges.mp ((S.mem_edgeTris).mp i.property))
      have hj := (mem_triEdges.mp ((S.mem_edgeTris).mp j.property))
      have hTi := eq_triple_of_mem (S.card_tri i) hi.1 hi.2.1 (hf i).1
        hxy (hf i).2.1.symm (hf i).2.2.symm
      have hTj := eq_triple_of_mem (S.card_tri j) hj.1 hj.2.1 (hf j).1
        hxy (hf j).2.1.symm (hf j).2.2.symm
      rw [hTi, hTj, hij]
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hfInj

include S in
theorem total_triangles_le_vertices_cube : (m : ℝ) ≤ (Fintype.card V : ℝ)^3 := by
  by_cases hn : Fintype.card V = 0
  · have hm : m = 0 := by
      by_contra hm
      have hi : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
      have hc := card_le_univ (S.tri hi)
      rw [S.card_tri, hn] at hc
      omega
    simp [hm]
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hload : ∀ e : Sym2 V,
      ∑ i : Fin m, (if e ∈ triEdges (S.tri i) then (1 : ℝ)/Fintype.card V else 0) ≤ 1 := by
    intro e
    have hc : ((S.edgeTris e).card : ℝ) ≤ Fintype.card V :=
      by exact_mod_cast S.edgeTris_card_le_vertices e
    have he : (∑ i : Fin m, if e ∈ triEdges (S.tri i) then (1 : ℝ)/Fintype.card V else 0) =
        ((S.edgeTris e).card : ℝ)/Fintype.card V := by
      calc (∑ i : Fin m, if e ∈ triEdges (S.tri i) then (1 : ℝ)/Fintype.card V else 0)
          = ∑ i ∈ S.edgeTris e, (1 : ℝ)/Fintype.card V := by rw [edgeTris, sum_filter]
        _ = ((S.edgeTris e).card : ℝ)/Fintype.card V := by simp [div_eq_mul_inv]
    rw [he]
    exact (div_le_one hnpos).mpr hc
  have hs := TypedTriangle.WeightedClone.fractional_total_mass_cap
    (fun i => triEdges (S.tri i)) (fun _ => (1 : ℝ)/Fintype.card V)
    (by intro i; positivity)
    (fun i => card_pos.mp (by rw [card_triEdges (S.card_tri i)]; norm_num)) hload
  simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin, mul_one_div] at hs
  have hcard : (Fintype.card (Sym2 V) : ℝ) ≤ (Fintype.card V : ℝ)^2 := by
    have hh := Fintype.card_le_of_surjective (Sym2.mk (α:=V)).uncurry Sym2.mk_surjective
    have hh' : Fintype.card (Sym2 V) ≤ (Fintype.card V)^2 := by simpa [pow_two] using hh
    exact_mod_cast hh'
  have hh := (div_le_iff₀ hnpos).mp hs
  have hm := mul_le_mul_of_nonneg_right hcard hnpos.le
  nlinarith

theorem card_star_edgesOf (P : Finset (Fin m)) (hP : IsPacking S P) (v : V) :
    (star (edgesOf S P) v).card = 2 * (P.filter fun i => v ∈ S.tri i).card := by
  unfold edgesOf
  rw [S.star_biUnion, card_biUnion]
  · rw [sum_congr rfl (fun i hi => S.card_star_triEdges (mem_filter.mp hi).2),
      sum_const, smul_eq_mul, mul_comm]
  · intro i hi j hj hij
    exact disjoint_of_subset_left (filter_subset _ _)
      (disjoint_of_subset_right (filter_subset _ _)
        (hP i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij))

#print axioms edgeTris_card_le_vertices
#print axioms total_triangles_le_vertices_cube
#print axioms card_star_edgesOf
end PartitionedTriangleAbsorption.Nibble.TriSystem
