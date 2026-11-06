/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.PhysicalGrouping

@[expose] public section

/-!
# V14 (S26 §6): el conteo de frontera se conserva al agrupar

Para un predicado arbitrario de uso `U i v` (la ficha `i` usa `v`), un bloque usa `v` si
ALGUNA ficha del bloque lo usa. Si los bloques son disjuntos dos a dos, el número de bloques
que usan `v` es `≤` el número de fichas que usan `v` (los bloques vacíos no usan nada, así que
la no vacuidad no se necesita).

Para el soporte del vector suma de un bloque basta una inclusión en esa unión (la cancelación
puede reducir el soporte). Consecuencias: conteo puntual, conteo total y normas `ℓ¹` (sobre
cualquier conjunto finito de coordenadas).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle.Grouping

variable {ι V : Type*} [Fintype ι]

/-- **Conteo de frontera bajo agrupación (predicado arbitrario).** -/
theorem card_blocks_using_le (P : Finset (Finset ι)) (hP : (P : Set (Finset ι)).PairwiseDisjoint id)
    (U : ι → V → Prop) [∀ i v, Decidable (U i v)] (v : V) :
    #(P.filter fun J => ∃ i ∈ J, U i v) ≤ #(Finset.univ.filter fun i => U i v) := by
  set P' := P.filter fun J => ∃ i ∈ J, U i v
  have h1 : #P' ≤ ∑ J ∈ P', #(J.filter fun i => U i v) := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun J hJ => ?_
    obtain ⟨-, i, hi, hU⟩ := Finset.mem_filter.1 hJ
    exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, hU⟩⟩
  have h2 : ∑ J ∈ P', #(J.filter fun i => U i v) = #(P'.biUnion fun J => J.filter fun i => U i v) := by
    rw [Finset.card_biUnion]
    intro J hJ K hK hJK
    exact Finset.disjoint_filter_filter
      (hP (Finset.mem_filter.1 hJ).1 (Finset.mem_filter.1 hK).1 hJK)
  have h3 : (P'.biUnion fun J => J.filter fun i => U i v) ⊆ Finset.univ.filter fun i => U i v := by
    intro i hi
    obtain ⟨J, -, hiJ⟩ := Finset.mem_biUnion.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hiJ).2⟩
  exact h1.trans (h2 ▸ Finset.card_le_card h3)

variable {W : Type*} (b : ι → W → ℤ)

omit [Fintype ι] in
/-- **Soporte del vector suma de un bloque:** inclusión en la unión de los soportes. -/
lemma blockSum_support_subset (J : Finset ι) (w : W) (h : (∑ i ∈ J, b i) w ≠ 0) :
    ∃ i ∈ J, b i w ≠ 0 := by
  rw [Finset.sum_apply] at h
  exact Finset.exists_ne_zero_of_sum_ne_zero h

/-- **Conteo puntual para el soporte real de las sumas de bloque.** -/
theorem card_blocks_support_le (P : Finset (Finset ι))
    (hP : (P : Set (Finset ι)).PairwiseDisjoint id) (w : W) :
    #(P.filter fun J => (∑ i ∈ J, b i) w ≠ 0) ≤ #(Finset.univ.filter fun i => b i w ≠ 0) := by
  refine le_trans (Finset.card_le_card ?_) (card_blocks_using_le P hP (fun i w => b i w ≠ 0) w)
  intro J hJ
  obtain ⟨hJP, hJw⟩ := Finset.mem_filter.1 hJ
  exact Finset.mem_filter.2 ⟨hJP, blockSum_support_subset b J w hJw⟩

/-- **Conteo total** sobre cualquier conjunto finito `S` de coordenadas. -/
theorem sum_card_blocks_support_le (P : Finset (Finset ι))
    (hP : (P : Set (Finset ι)).PairwiseDisjoint id) (S : Finset W) :
    ∑ w ∈ S, #(P.filter fun J => (∑ i ∈ J, b i) w ≠ 0) ≤
      ∑ w ∈ S, #(Finset.univ.filter fun i => b i w ≠ 0) :=
  Finset.sum_le_sum fun w _ => card_blocks_support_le b P hP w

/-- Norma `ℓ¹` sobre un conjunto finito de coordenadas `S`. -/
def normOn (S : Finset W) (x : W → ℤ) : ℤ := ∑ w ∈ S, |x w|

omit [Fintype ι] in
/-- Desigualdad triangular para la suma de un bloque. -/
lemma normOn_blockSum_le (S : Finset W) (J : Finset ι) :
    normOn S (∑ i ∈ J, b i) ≤ ∑ i ∈ J, normOn S (b i) := by
  unfold normOn
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [Finset.sum_apply]
  exact Finset.abs_sum_le_sum_abs _ _

omit [Fintype ι] in
/-- Cota de norma de un bloque por su cardinal: `‖∑_{J} b i‖ ≤ #J · C`. -/
lemma normOn_blockSum_le_card_mul (S : Finset W) (J : Finset ι) (C : ℤ)
    (hC : ∀ i ∈ J, normOn S (b i) ≤ C) :
    normOn S (∑ i ∈ J, b i) ≤ #J * C := by
  refine (normOn_blockSum_le b S J).trans ?_
  have := Finset.sum_le_sum hC
  simpa [Finset.sum_const, nsmul_eq_mul] using this

/-- **Norma total:** la suma de las normas de los bloques está acotada por la de las fichas. -/
theorem sum_normOn_blocks_le (P : Finset (Finset ι))
    (hP : (P : Set (Finset ι)).PairwiseDisjoint id) (S : Finset W) :
    ∑ J ∈ P, normOn S (∑ i ∈ J, b i) ≤ ∑ i, normOn S (b i) := by
  have hnn : ∀ i, 0 ≤ normOn S (b i) := fun i =>
    Finset.sum_nonneg fun w _ => abs_nonneg _
  calc ∑ J ∈ P, normOn S (∑ i ∈ J, b i) ≤ ∑ J ∈ P, ∑ i ∈ J, normOn S (b i) :=
        Finset.sum_le_sum fun J _ => normOn_blockSum_le b S J
    _ = ∑ i ∈ P.biUnion id, normOn S (b i) := by
        rw [Finset.sum_biUnion hP]; rfl
    _ ≤ ∑ i, normOn S (b i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hnn i

/-- **Paquete para una `Finpartition` producida por la agrupación:** conteo puntual de
soporte, conteo total y normas, con la cota uniforme de cardinal `N` en cada bloque. -/
theorem grouping_frontier_package (Q : Finpartition (Finset.univ : Finset ι)) (N : ℕ)
    (hN : ∀ J ∈ Q.parts, #J ≤ N) (S : Finset W) (C : ℤ) (hC : ∀ i, normOn S (b i) ≤ C)
    (hC0 : 0 ≤ C) :
    (∀ w, #(Q.parts.filter fun J => (∑ i ∈ J, b i) w ≠ 0) ≤
        #(Finset.univ.filter fun i => b i w ≠ 0)) ∧
    (∑ w ∈ S, #(Q.parts.filter fun J => (∑ i ∈ J, b i) w ≠ 0) ≤
        ∑ w ∈ S, #(Finset.univ.filter fun i => b i w ≠ 0)) ∧
    (∑ J ∈ Q.parts, normOn S (∑ i ∈ J, b i) ≤ ∑ i, normOn S (b i)) ∧
    (∀ J ∈ Q.parts, normOn S (∑ i ∈ J, b i) ≤ N * C) := by
  refine ⟨fun w => card_blocks_support_le b _ Q.disjoint w,
    sum_card_blocks_support_le b _ Q.disjoint S, sum_normOn_blocks_le b _ Q.disjoint S,
    fun J hJ => ?_⟩
  refine (normOn_blockSum_le_card_mul b S J C fun i _ => hC i).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN J hJ) hC0

end TypedTriangle.Grouping
