/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Defs

@[expose] public section

/-!
# Hechos elementales demostrados

* `mem_triEdges` : descripción de las aristas de un conjunto de vértices.
* `isDecomposition_empty` : el grafo sin aristas tiene la descomposición vacía.
* `isPhysical_of_isDecomposition` : (H2) es necesaria (física de los conjuntos descomponibles).
* `exists_fractional_of_isDecomposition` : la existencia de un peso fraccional no negativo
  es necesaria.
* `hinge_order_ge_six` : toda bisagra contiene las cuatro raíces y tiene orden al menos seis.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

omit [Fintype V] in
lemma mem_triEdges {T : Finset V} {p q : V} :
    s(p, q) ∈ triEdges T ↔ p ∈ T ∧ q ∈ T ∧ p ≠ q := by
  simp [triEdges, and_assoc]

omit [Fintype V] in
lemma IsDecomposition.subset {H : Host V I} {F : Set (Multiset I)} {J : Finset (Sym2 V)}
    {D : Finset (Finset V)} (hD : IsDecomposition H F J D) {T : Finset V} (hT : T ∈ D) :
    triEdges T ⊆ J := by
  rw [← hD.2.2]; exact Finset.subset_biUnion_of_mem _ hT

omit [Fintype V] in
lemma IsDecomposition.exists_mem {H : Host V I} {F : Set (Multiset I)} {J : Finset (Sym2 V)}
    {D : Finset (Finset V)} (hD : IsDecomposition H F J D) {e : Sym2 V} (he : e ∈ J) :
    ∃ T ∈ D, e ∈ triEdges T := by
  rw [← hD.2.2, Finset.mem_biUnion] at he; exact he

omit [Fintype V] in
lemma IsDecomposition.unique {H : Host V I} {F : Set (Multiset I)} {J : Finset (Sym2 V)}
    {D : Finset (Finset V)} (hD : IsDecomposition H F J D) {e : Sym2 V} {T T' : Finset V}
    (hT : T ∈ D) (hT' : T' ∈ D) (he : e ∈ triEdges T) (he' : e ∈ triEdges T') : T = T' := by
  by_contra hne
  exact Finset.disjoint_left.mp (hD.2.1 hT hT' hne) he he'

/-- El grafo sin aristas tiene la descomposición vacía. -/
theorem isDecomposition_empty (H : Host V I) (F : Set (Multiset I)) (hG : H.G = ⊥) :
    IsDecomposition H F (edges H) ∅ := by
  refine ⟨by simp, by simp, ?_⟩
  ext e; simp [edges, hG]

omit [Fintype V] in
/-- Si `J` admite una descomposición permitida, entonces `J` es físico. En particular la
hipótesis (H2) es necesaria para la conclusión (T1). -/
theorem isPhysical_of_isDecomposition {H : Host V I} {F : Set (Multiset I)}
    {J : Finset (Sym2 V)} {D : Finset (Finset V)} (hD : IsDecomposition H F J D) :
    IsPhysical H F J := by
  have key : ind J = ∑ T ∈ D, ind (triEdges T) := by
    funext e
    simp only [Finset.sum_apply, ind]
    by_cases he : e ∈ J
    · obtain ⟨T, hT, heT⟩ := hD.exists_mem he
      rw [if_pos he, Finset.sum_eq_single T]
      · simp [heT]
      · intro T' hT' hne
        rw [if_neg]; intro h'; exact hne (hD.unique hT' hT h' heT)
      · intro h; exact absurd hT h
    · rw [if_neg he]; symm
      apply Finset.sum_eq_zero
      intro T hT
      rw [if_neg]; intro h'; exact he (hD.subset hT h')
  unfold IsPhysical lattice
  rw [key]
  apply Submodule.sum_mem
  intro T hT
  exact Submodule.subset_span ⟨T, hD.1 T hT, rfl⟩

/-- Una descomposición da un peso fraccional no negativo (su indicador) con carga uno en
cada arista: la existencia de tal peso es necesaria. -/
theorem exists_fractional_of_isDecomposition {H : Host V I} {F : Set (Multiset I)}
    {D : Finset (Finset V)} (hD : IsDecomposition H F (edges H) D) :
    ∃ φ : Finset V → ℝ, (∀ T, 0 ≤ φ T) ∧
      ∀ e ∈ H.G.edgeSet, ∑ T ∈ (allowed H F).filter (fun T => e ∈ triEdges T), φ T = 1 := by
  refine ⟨fun T => if T ∈ D then 1 else 0, fun T => by dsimp only; split_ifs <;> norm_num, ?_⟩
  intro e he
  have he' : e ∈ edges H := by simp [edges, he]
  obtain ⟨T, hT, heT⟩ := hD.exists_mem he'
  rw [Finset.sum_eq_single T]
  · simp [hT]
  · intro T' hT' hne
    rw [if_neg]; intro h'
    exact hne (hD.unique h' hT (Finset.mem_filter.mp hT').2 heT)
  · intro h
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD.1 T hT⟩,
      heT⟩) h

omit [Fintype V] in
lemma distinct_of_card_three {u v a : V} (h : ({u, v, a} : Finset V).card = 3) :
    u ≠ v ∧ u ≠ a ∧ v ≠ a := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have := Finset.card_le_two (a := u) (b := a); simp_all
  · have := Finset.card_le_two (a := u) (b := v)
    rw [show ({u, v, u} : Finset V) = {u, v} by ext; simp; tauto] at h; omega
  · have := Finset.card_le_two (a := u) (b := v); simp_all

omit [Fintype V] in
/-- En una descomposición, toda arista `pq` del conjunto descompuesto está en un triángulo
`T ∈ D` cuyo tercer vértice `x` da aristas `px, qx` también en el conjunto. -/
lemma IsDecomposition.third {H : Host V I} {F : Set (Multiset I)} {K : Finset (Sym2 V)}
    {D : Finset (Finset V)} (hD : IsDecomposition H F K D) {p q : V} (hpq : s(p, q) ∈ K) :
    ∃ T ∈ D, ∃ x, p ∈ T ∧ q ∈ T ∧ x ∈ T ∧ x ≠ p ∧ x ≠ q ∧
      s(p, x) ∈ K ∧ s(q, x) ∈ K := by
  obtain ⟨T, hT, hpqT⟩ := hD.exists_mem hpq
  rw [mem_triEdges] at hpqT
  obtain ⟨hp, hq, hne⟩ := hpqT
  have hc : ((T.erase p).erase q).card = 1 := by
    rw [Finset.card_erase_of_mem (by simp [hq, Ne.symm hne]),
      Finset.card_erase_of_mem hp, (hD.1 T hT).1]
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < ((T.erase p).erase q).card)
  simp only [Finset.mem_erase] at hx
  obtain ⟨hxq, hxp, hxT⟩ := hx
  refine ⟨T, hT, x, hp, hq, hxT, hxp, hxq, ?_, ?_⟩
  · exact hD.subset hT (mem_triEdges.mpr ⟨hp, hxT, Ne.symm hxp⟩)
  · exact hD.subset hT (mem_triEdges.mpr ⟨hq, hxT, Ne.symm hxq⟩)

omit [Fintype V] in
lemma card_four_le_three {T : Finset V} {u v a x : V} (hT : T.card = 3)
    (hu : u ∈ T) (hv : v ∈ T) (ha : a ∈ T) (hx : x ∈ T)
    (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hxu : x ≠ u) (hxv : x ≠ v) (hxa : x ≠ a) :
    False := by
  have hsub : ({u, v, a, x} : Finset V) ⊆ T := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  have h4 : ({u, v, a, x} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [huv, hua, Ne.symm hxu]),
      Finset.card_insert_of_notMem (by simp [hva, Ne.symm hxv]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hxa]), Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

/-- Toda bisagra física para `T_a = {u,v,a}`, `T_b = {u,v,b}` contiene en su soporte las
cuatro raíces `u, v, a, b` y tiene orden al menos seis. -/
theorem hinge_order_ge_six {H : Host V I} {F : Set (Multiset I)} {u v a b : V}
    {J : Finset (Sym2 V)} (hab : a ≠ b) (hTa : IsAllowed H F {u, v, a})
    (hTb : IsAllowed H F {u, v, b}) (hJ : IsHinge H F u v a b J) :
    ({u, v, a, b} : Finset V) ⊆ support J ∧ 6 ≤ (support J).card := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := distinct_of_card_three hTb.1
  obtain ⟨-, hdisj, ⟨D1, hD1⟩, ⟨D2, hD2⟩⟩ := hJ
  have notJ : ∀ e, e ∈ triEdges {u, v, a} ∪ triEdges {u, v, b} → e ∉ J :=
    fun e he hJe => Finset.disjoint_left.mp hdisj hJe he
  have huvJ : s(u, v) ∉ J := notJ _ (Finset.mem_union_left _ (mem_triEdges.mpr ⟨by simp, by simp, huv⟩))
  have hubJ : s(u, b) ∉ J := notJ _ (Finset.mem_union_right _ (mem_triEdges.mpr ⟨by simp, by simp, hub⟩))
  have hvbJ : s(v, b) ∉ J := notJ _ (Finset.mem_union_right _ (mem_triEdges.mpr ⟨by simp, by simp, hvb⟩))
  -- modo a, arista `ua`
  obtain ⟨T1, hT1, x, huT1, haT1, hxT1, hxu, hxa, hux, hax⟩ :=
    hD1.third (p := u) (q := a) (by simp [wedge])
  have hxv : x ≠ v := by
    intro h; rw [h] at hux; simp [wedge, huvJ, huv, hua, hva] at hux
  have hxb : x ≠ b := by
    intro h; rw [h] at hux; simp [wedge, hubJ, huv, hua, Ne.symm hab] at hux
  have hux' : s(u, x) ∈ J := by
    simpa [wedge, Sym2.eq_iff, hxa, huv, hua] using hux
  have hax' : s(a, x) ∈ J := by
    simpa [wedge, Sym2.eq_iff, hxu, hxv, hxa] using hax
  -- modo a, arista `va`
  obtain ⟨T2, hT2, y, hvT2, haT2, hyT2, hyv, hya, hvy, hay⟩ :=
    hD1.third (p := v) (q := a) (by simp [wedge])
  have hyu : y ≠ u := by
    intro h; rw [h, Sym2.eq_swap] at hvy; simp [wedge, huvJ, huv, hua, hva, Ne.symm huv] at hvy
  have hyb : y ≠ b := by
    intro h; rw [h] at hvy; simp [wedge, hvbJ, hva, Ne.symm hab] at hvy
  have hvy' : s(v, y) ∈ J := by
    simpa [wedge, Sym2.eq_iff, hya, huv, Ne.symm huv, hva] using hvy
  have hxy : x ≠ y := by
    rintro rfl
    have h1 : s(a, x) ∈ triEdges T1 := mem_triEdges.mpr ⟨haT1, hxT1, Ne.symm hxa⟩
    have h2 : s(a, x) ∈ triEdges T2 := mem_triEdges.mpr ⟨haT2, hyT2, Ne.symm hxa⟩
    have hT12 := hD1.unique hT1 hT2 h1 h2
    subst hT12
    exact card_four_le_three (hD1.1 T1 hT1).1 huT1 hvT2 haT1 hxT1 huv hua hva hxu hxv hxa
  -- modo b, arista `ub`
  obtain ⟨T3, hT3, z, -, -, -, hzu, hzb, huz, hbz⟩ :=
    hD2.third (p := u) (q := b) (by simp [wedge])
  have hzv : z ≠ v := by
    intro h; rw [h] at huz; simp [wedge, huvJ, huv, hub, hvb] at huz
  have hbz' : s(b, z) ∈ J := by
    simpa [wedge, Sym2.eq_iff, hzu, hzv, hzb] using hbz
  have hsub : ({u, v, a, b, x, y} : Finset V) ⊆ support J := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, hux', Sym2.mem_mk_left _ _⟩
    · exact ⟨_, hvy', Sym2.mem_mk_left _ _⟩
    · exact ⟨_, hax', Sym2.mem_mk_left _ _⟩
    · exact ⟨_, hbz', Sym2.mem_mk_left _ _⟩
    · exact ⟨_, hux', Sym2.mem_mk_right _ _⟩
    · exact ⟨_, hvy', Sym2.mem_mk_right _ _⟩
  refine ⟨fun w hw => hsub (by simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢; tauto), ?_⟩
  have h6 : ({u, v, a, b, x, y} : Finset V).card = 6 := by
    rw [Finset.card_insert_of_notMem (by simp [huv, hua, hub, Ne.symm hxu, Ne.symm hyu]),
      Finset.card_insert_of_notMem (by simp [hva, hvb, Ne.symm hxv, Ne.symm hyv]),
      Finset.card_insert_of_notMem (by simp [hab, Ne.symm hxa, Ne.symm hya]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hxb, Ne.symm hyb]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

end TypedTriangle
