/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.PaschTools
public import RequestProject.TypedTriangle.PaschRootedInfluence

/-! # Parity excludes exactly three Latin blocks in a Pasch

Three transversal triples force the fourth to be transversal. The input is
only the defining degree-two property of a Pasch, not a decomposition theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical TypedTriangle
variable {V : Type*} [DecidableEq V]

theorem sum_vertex_weights (S : Finset (Finset V)) (f : V → ℕ) :
    ∑ T ∈ S, ∑ v ∈ T, f v =
      ∑ v ∈ S.biUnion id, f v * #(S.filter (fun T => v ∈ T)) := by
  have hlocal : ∀ T ∈ S, ∑ v ∈ T, f v =
      ∑ v ∈ S.biUnion id, if v ∈ T then f v else 0 := by
    intro T hT
    rw [sum_ite_mem]
    congr 1
    ext v
    simp only [mem_inter, mem_biUnion, id]
    exact ⟨fun hv => ⟨⟨T, hT, hv⟩, hv⟩, fun hv => hv.2⟩
  rw [sum_congr rfl hlocal, sum_comm]
  apply sum_congr rfl
  intro v _
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  simp only [Nat.cast_id]

theorem even_label_incidence {S : Finset (Finset V)} (hS : Pasch.IsPasch S)
    (P : V → Prop) [DecidablePred P] : Even (∑ T ∈ S, #(T.filter P)) := by
  have hh := sum_vertex_weights S (fun v => if P v then 1 else 0)
  have hleft : (∑ T ∈ S, ∑ v ∈ T, if P v then 1 else 0) = ∑ T ∈ S, #(T.filter P) := by
    apply sum_congr rfl
    intro T _
    rw [← sum_filter]
    simp
  rw [hleft] at hh
  have hright : (∑ v ∈ S.biUnion id, (if P v then 1 else 0) * #(S.filter (fun T => v ∈ T))) =
      2 * #((S.biUnion id).filter P) := by
    calc
      _ = ∑ v ∈ S.biUnion id, if P v then 2 else 0 := by
        apply sum_congr rfl
        intro v hv
        rw [hS.2.2.2.1 v hv]
        split_ifs <;> norm_num
      _ = _ := by rw [← sum_filter]; simp [mul_comm]
  rw [hright] at hh
  exact ⟨#((S.biUnion id).filter P), by omega⟩

def IsPartite (part : V → Option (Fin 3)) (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ i : Fin 3, #(T.filter (fun v => part v = some i)) = 1

theorem fourth_partite {S K : Finset (Finset V)} (hS : Pasch.IsPasch S)
    (part : V → Option (Fin 3)) (hK : K.card = 3)
    (hpart : ∀ T ∈ K, IsPartite part T) {T : Finset V} (hTK : T ∉ K)
    (hSK : S = insert T K) : IsPartite part T := by
  have hTS : T ∈ S := by rw [hSK]; simp
  have hpos : ∀ i : Fin 3, 0 < #(T.filter (fun v => part v = some i)) := by
    intro i
    have hev := even_label_incidence hS (fun v => part v = some i)
    rw [hSK, sum_insert hTK] at hev
    have hsum : (∑ Q ∈ K, #(Q.filter (fun v => part v = some i))) = 3 := by
      rw [sum_congr rfl (fun Q hQ => (hpart Q hQ).2 i)]
      simp [hK]
    rw [hsum] at hev
    obtain ⟨a, ha⟩ := hev
    omega
  obtain ⟨u, hu⟩ := card_pos.mp (hpos 0)
  obtain ⟨v, hv⟩ := card_pos.mp (hpos 1)
  obtain ⟨w, hw⟩ := card_pos.mp (hpos 2)
  obtain ⟨huT, hu⟩ := mem_filter.mp hu
  obtain ⟨hvT, hv⟩ := mem_filter.mp hv
  obtain ⟨hwT, hw⟩ := mem_filter.mp hw
  have huv : u ≠ v := by intro he; subst v; simp_all
  have huw : u ≠ w := by intro he; subst w; simp_all
  have hvw : v ≠ w := by intro he; subst w; simp_all
  have heq : T = {u, v, w} := by
    symm
    apply eq_of_subset_of_card_le
      (insert_subset_iff.mpr ⟨huT, insert_subset_iff.mpr ⟨hvT, singleton_subset_iff.mpr hwT⟩⟩)
    rw [hS.2.1 T hTS]
    simp [huv, huw, hvw]
  refine ⟨hS.2.1 T hTS, fun i => ?_⟩
  rw [heq]
  fin_cases i <;> simp [filter_insert, filter_singleton, hu, hv, hw, huv, huw, hvw]

theorem no_three_partite_blocks (part : V → Option (Fin 3))
    (R Q : Finset (Finset V)) (hR : ∀ T ∈ R, ¬ IsPartite part T)
    (hQ : ∀ T ∈ Q, IsPartite part T) {S : Finset (Finset V)}
    (hS : Pasch.IsPasch S) (hsub : S ⊆ R ∪ Q) : (S ∩ Q).card ≠ 3 := by
  intro hthree
  let K := S ∩ Q
  have hKS : K ⊆ S := inter_subset_left
  have hsingle : (S \ K).card = 1 := by rw [card_sdiff_of_subset hKS, hS.1, hthree]
  obtain ⟨T, hT⟩ := card_eq_one.mp hsingle
  have hTM : T ∈ S \ K := by rw [hT]; simp
  have hSK : S = insert T K := by
    calc
      S = (S \ K) ∪ K := (sdiff_union_of_subset hKS).symm
      _ = _ := by rw [hT]; simp
  have hpart := fourth_partite hS part hthree
    (fun A hA => hQ A (mem_inter.mp hA).2) (mem_sdiff.mp hTM).2 hSK
  rcases mem_union.mp (hsub (mem_sdiff.mp hTM).1) with hTR | hTQ
  · exact hR T hTR hpart
  · exact (mem_sdiff.mp hTM).2 (mem_inter.mpr ⟨(mem_sdiff.mp hTM).1, hTQ⟩)

end CDRBicolour.KBicolor.LatinPasch
