/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Lattice

@[expose] public section

/-!
# Bisagras, transformers, absorbedores y ensamblaje final (P03 parcial, P14 parcial, P20)

Resultados combinatorios exactos (todos demostrados):

* `triEdges_eq_insert_wedge`: `E(T_a) = {uv} ∪̇ W_a`;
* `IsHinge.isTransformer`, `IsTransformer.sub_mem_lattice`, `hinge_sub_mem_lattice`:
  una bisagra transforma la cuña `W_a` en `W_b`, y por tanto
  `1_{T_a} − 1_{T_b} ∈ Λ_G` (paso «la diferencia de sus dos modos certifica `T − uvc`» de
  S05 §2);
* `IsTransformer.compose`: composición de transformers (cadena de bisagras de S05, S27);
* `IsTransformer.absorbs`: un transformer `J : P → Q` con `J ∪ Q` ya cubierto por un grafo
  basal da un absorbedor;
* `absorber_union`: ensamblaje del absorbedor terminal de P14 (S18): absorbedores
  disjuntos para cada candidato se unen en un único grafo basal `A` que absorbe cada uno;
* `assembly_P20`: ensamblaje final de P20 (S24 §§3–4): packings disjuntos más un modo
  terminal de `A ∪̇ G_ℓ` dan una descomposición de todo el host.

La construcción misma de los absorbedores (G2 para familias generales, S02/S27) y la
existencia de la cadena de packings (P07–P19) NO están formalizadas aquí.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

omit [Fintype V] in
lemma triEdges_eq_insert_wedge {u v a : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) :
    triEdges ({u, v, a} : Finset V) = insert s(u, v) (wedge u v a) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_triEdges]
    simp only [wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨hx, hy, hxy⟩
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> tauto
    · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [Ne.symm]

omit [Fintype V] in
lemma not_mem_wedge {u v a : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) :
    s(u, v) ∉ wedge u v a := by
  simp only [wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
  tauto

/-- `J` es un transformer de `P` en `Q`: disjunto de ambos y `J ∪ P`, `J ∪ Q` basales.
Los bordes `P`, `Q` no necesitan ser físicos por separado. -/
def IsTransformer (H : Host V I) (F : Set (Multiset I)) (J P Q : Finset (Sym2 V)) : Prop :=
  Disjoint J P ∧ Disjoint J Q ∧ (∃ D, IsDecomposition H F (J ∪ P) D) ∧
    (∃ D, IsDecomposition H F (J ∪ Q) D)

/-- Una bisagra para `T_a, T_b` es un transformer de la cuña `W_a` en la cuña `W_b`. -/
theorem IsHinge.isTransformer {H : Host V I} {F : Set (Multiset I)} {u v a b : V}
    {J : Finset (Sym2 V)} (hJ : IsHinge H F u v a b J) (huv : u ≠ v) (hua : u ≠ a)
    (hva : v ≠ a) (hub : u ≠ b) (hvb : v ≠ b) :
    IsTransformer H F J (wedge u v a) (wedge u v b) := by
  obtain ⟨-, hdisj, hDa, hDb⟩ := hJ
  refine ⟨?_, ?_, hDa, hDb⟩
  · refine Finset.disjoint_of_subset_right ?_ hdisj
    intro e he
    rw [triEdges_eq_insert_wedge huv hua hva]
    exact Finset.mem_union_left _ (Finset.mem_insert_of_mem he)
  · refine Finset.disjoint_of_subset_right ?_ hdisj
    intro e he
    rw [triEdges_eq_insert_wedge huv hub hvb]
    exact Finset.mem_union_right _ (Finset.mem_insert_of_mem he)

omit [Fintype V] in
/-- Los dos modos de un transformer certifican `1_P − 1_Q ∈ Λ_G`. -/
theorem IsTransformer.sub_mem_lattice {H : Host V I} {F : Set (Multiset I)}
    {J P Q : Finset (Sym2 V)} (hT : IsTransformer H F J P Q) :
    ind P - ind Q ∈ lattice H F := by
  obtain ⟨hJP, hJQ, ⟨D1, hD1⟩, ⟨D2, hD2⟩⟩ := hT
  have h1 := isPhysical_of_isDecomposition hD1
  have h2 := isPhysical_of_isDecomposition hD2
  unfold IsPhysical at h1 h2
  rw [ind_union_of_disjoint hJP] at h1
  rw [ind_union_of_disjoint hJQ] at h2
  have := Submodule.sub_mem _ h1 h2
  rwa [add_sub_add_left_eq_sub] at this

/-- **Diferencia de bisagra.** Si existe una bisagra para `T_a = {u,v,a}` y
`T_b = {u,v,b}`, entonces `1_{E(T_a)} − 1_{E(T_b)} ∈ Λ_G`. -/
theorem hinge_sub_mem_lattice {H : Host V I} {F : Set (Multiset I)} {u v a b : V}
    {J : Finset (Sym2 V)} (hJ : IsHinge H F u v a b J) (hTa : IsAllowed H F {u, v, a})
    (hTb : IsAllowed H F {u, v, b}) :
    ind (triEdges ({u, v, a} : Finset V)) - ind (triEdges ({u, v, b} : Finset V)) ∈
      lattice H F := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := distinct_of_card_three hTb.1
  have h := (hJ.isTransformer huv hua hva hub hvb).sub_mem_lattice
  rw [triEdges_eq_insert_wedge huv hua hva, triEdges_eq_insert_wedge huv hub hvb,
    Finset.insert_eq, Finset.insert_eq,
    ind_union_of_disjoint (Finset.disjoint_singleton_left.2 (not_mem_wedge huv hua hva)),
    ind_union_of_disjoint (Finset.disjoint_singleton_left.2 (not_mem_wedge huv hub hvb)),
    add_sub_add_left_eq_sub]
  exact h

omit [Fintype V] in
/-- **Composición de transformers.** Si `J₁ : P → Q` y `J₂ : Q → R`, con `J₁, J₂, Q`
disjuntos dos a dos y `J₁` disjunto de `R`, `J₂` disjunto de `P`, entonces
`J₁ ∪ Q ∪ J₂ : P → R` siempre que `P` y `R` sean disjuntos de `Q`. No hace falta que
`P` y `R` sean disjuntos entre sí. -/
theorem IsTransformer.compose {H : Host V I} {F : Set (Multiset I)}
    {J₁ J₂ P Q R : Finset (Sym2 V)} (h₁ : IsTransformer H F J₁ P Q)
    (h₂ : IsTransformer H F J₂ Q R) (h12 : Disjoint J₁ J₂) (h1R : Disjoint J₁ R)
    (h2P : Disjoint J₂ P) (hPQ : Disjoint P Q) (hQR : Disjoint Q R) :
    IsTransformer H F (J₁ ∪ Q ∪ J₂) P R := by
  obtain ⟨h1P, h1Q, ⟨D1P, hD1P⟩, ⟨D1Q, hD1Q⟩⟩ := h₁
  obtain ⟨h2Q, h2R, ⟨D2Q, hD2Q⟩, ⟨D2R, hD2R⟩⟩ := h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨h1P, hPQ.symm⟩, h2P⟩
  · exact Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨h1R, hQR⟩, h2R⟩
  · -- (J₁ ∪ Q ∪ J₂) ∪ P = (J₁ ∪ P) ∪ (J₂ ∪ Q)
    have hd : Disjoint (J₁ ∪ P) (J₂ ∪ Q) :=
      Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨h12, h1Q⟩,
        Finset.disjoint_union_right.2 ⟨h2P.symm, hPQ⟩⟩
    refine ⟨D1P ∪ D2Q, ?_⟩
    have heq : J₁ ∪ Q ∪ J₂ ∪ P = (J₁ ∪ P) ∪ (J₂ ∪ Q) := by
      ext e; simp only [Finset.mem_union]; tauto
    rw [heq]; exact hD1P.union hD2Q hd
  · -- (J₁ ∪ Q ∪ J₂) ∪ R = (J₁ ∪ Q) ∪ (J₂ ∪ R)
    have hd : Disjoint (J₁ ∪ Q) (J₂ ∪ R) :=
      Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨h12, h1R⟩,
        Finset.disjoint_union_right.2 ⟨h2Q.symm, hQR⟩⟩
    refine ⟨D1Q ∪ D2R, ?_⟩
    have heq : J₁ ∪ Q ∪ J₂ ∪ R = (J₁ ∪ Q) ∪ (J₂ ∪ R) := by
      ext e; simp only [Finset.mem_union]; tauto
    rw [heq]; exact hD1Q.union hD2R hd

/-- `A` absorbe `P`: `A` es basal, disjunto de `P`, y `A ∪ P` es basal. -/
def IsAbsorber (H : Host V I) (F : Set (Multiset I)) (A P : Finset (Sym2 V)) : Prop :=
  Disjoint A P ∧ (∃ D, IsDecomposition H F A D) ∧ (∃ D, IsDecomposition H F (A ∪ P) D)

omit [Fintype V] in
/-- Un transformer `J : P → Q` con `J` y `Q` basales da un absorbedor `J ∪ Q` de `P`. -/
theorem IsTransformer.absorbs {H : Host V I} {F : Set (Multiset I)} {J P Q : Finset (Sym2 V)}
    (hT : IsTransformer H F J P Q) (hPQ : Disjoint P Q) (hQ : ∃ D, IsDecomposition H F Q D)
    (hJdec : ∃ D, IsDecomposition H F J D) : IsAbsorber H F (J ∪ Q) P := by
  obtain ⟨hJP, hJQ, ⟨DP, hDP⟩, -⟩ := hT
  obtain ⟨DQ, hDQ⟩ := hQ
  obtain ⟨DJ, hDJ⟩ := hJdec
  refine ⟨Finset.disjoint_union_left.2 ⟨hJP, hPQ.symm⟩, ⟨DJ ∪ DQ, hDJ.union hDQ hJQ⟩,
    ⟨DP ∪ DQ, ?_⟩⟩
  have heq : J ∪ Q ∪ P = (J ∪ P) ∪ Q := by ext e; simp only [Finset.mem_union]; tauto
  rw [heq]
  exact hDP.union hDQ (Finset.disjoint_union_left.2 ⟨hJQ, hPQ⟩)

omit [Fintype V] in
/-- **Absorbedor terminal (P14, ensamblaje).** Sea una familia finita de candidatos `P j`
y absorbedores `A j` disjuntos dos a dos, cada `A i` disjunto de cada candidato `P j`.
Entonces la unión `A = ⋃ A j` es basal y absorbe cada candidato. -/
theorem absorber_union {H : Host V I} {F : Set (Multiset I)} {ι : Type*} (s : Finset ι)
    (A P : ι → Finset (Sym2 V)) (hA : ∀ j ∈ s, IsAbsorber H F (A j) (P j))
    (hdisj : (s : Set ι).PairwiseDisjoint A) (hAP : ∀ i ∈ s, ∀ j ∈ s, Disjoint (A i) (P j)) :
    (∃ D, IsDecomposition H F (s.biUnion A) D) ∧
      ∀ j ∈ s, IsAbsorber H F (s.biUnion A) (P j) := by
  have hA1 : ∀ j ∈ s, ∃ D, IsDecomposition H F (A j) D := fun j hj => (hA j hj).2.1
  have hA2 : ∀ j ∈ s, ∃ D, IsDecomposition H F (A j ∪ P j) D := fun j hj => (hA j hj).2.2
  choose! DA hDA using hA1
  choose! DP hDP using hA2
  refine ⟨⟨_, isDecomposition_biUnion s A DA hDA hdisj⟩, fun j hj => ?_⟩
  refine ⟨(Finset.disjoint_biUnion_left _ _ _).2 fun i hi => hAP i hi j hj,
    ⟨_, isDecomposition_biUnion s A DA hDA hdisj⟩, ?_⟩
  -- A ∪ P j = (A j ∪ P j) ∪ ⋃_{i ≠ j} A i
  have hrest := isDecomposition_biUnion (s.erase j) A DA
    (fun i hi => hDA i (Finset.mem_of_mem_erase hi)) (hdisj.subset (by simp))
  have hd : Disjoint (A j ∪ P j) ((s.erase j).biUnion A) := by
    rw [Finset.disjoint_biUnion_right]
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    exact Finset.disjoint_union_left.2 ⟨hdisj hj (Finset.mem_of_mem_erase hi) (Ne.symm hij),
      (hAP i (Finset.mem_of_mem_erase hi) j hj).symm⟩
  refine ⟨DP j ∪ (s.erase j).biUnion DA, ?_⟩
  have heq : s.biUnion A ∪ P j = (A j ∪ P j) ∪ (s.erase j).biUnion A := by
    ext e
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_erase]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · by_cases hij : i = j
        · subst hij; exact Or.inl (Or.inl h)
        · exact Or.inr ⟨i, ⟨hij, hi⟩, h⟩
      · exact Or.inl (Or.inr h)
    · rintro ((h | h) | ⟨i, ⟨-, hi⟩, h⟩)
      · exact Or.inl ⟨j, hj, h⟩
      · exact Or.inr h
      · exact Or.inl ⟨i, hi, h⟩
  rw [heq]
  exact (hDP j hj).union hrest hd

/-- **Ensamblaje final (P20).** Si las aristas del host son la unión disjunta de las aristas
cubiertas por packings `P i` (`i ∈ s`), de un absorbedor `A` y del residuo terminal `L`, y
`A ∪ L` es basal, entonces el host admite una descomposición permitida. -/
theorem assembly_P20 {H : Host V I} {F : Set (Multiset I)} {ι : Type*} (s : Finset ι)
    (P : ι → Finset (Finset V)) (hP : ∀ i ∈ s, (∀ T ∈ P i, IsAllowed H F T) ∧
      ((P i : Set (Finset V)).PairwiseDisjoint triEdges))
    (hdisj : (s : Set ι).PairwiseDisjoint (fun i => (P i).biUnion triEdges))
    (A L : Finset (Sym2 V))
    (hterm : ∃ D, IsDecomposition H F (A ∪ L) D)
    (hsep : Disjoint (s.biUnion fun i => (P i).biUnion triEdges) (A ∪ L))
    (hcover : (s.biUnion fun i => (P i).biUnion triEdges) ∪ (A ∪ L) = edges H) :
    ∃ D, IsDecomposition H F (edges H) D := by
  obtain ⟨DT, hDT⟩ := hterm
  have hpk := isDecomposition_biUnion s (fun i => (P i).biUnion triEdges) P
    (fun i hi => ⟨(hP i hi).1, (hP i hi).2, rfl⟩) hdisj
  refine ⟨s.biUnion P ∪ DT, ?_⟩
  rw [← hcover]
  exact hpk.union hDT hsep

end TypedTriangle
