/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.QuotientBox

@[expose] public section

/-!
# V14 (S26 §6): agrupación uniforme de fichas con signo acotadas, conservando la torsión

Para `d B R : ℕ` fijos se define una constante `groupBound d B R ≥ 1`, elegida ANTES del
retículo y del número de fichas, tal que: si `Γ ≤ ℤ^d` está generado por vectores de la caja
`[-R,R]^d`, las fichas `z i ∈ [-B,B]^d` (índices de un tipo finito arbitrario, con repeticiones
permitidas) y `∑ i, z i ∈ Γ`, entonces el conjunto de índices posee una `Finpartition` en
bloques no vacíos y disjuntos de cardinal `≤ groupBound d B R`, con `∑_{i∈J} z i ∈ Γ` en cada
bloque.

Ruta (1) de la guía: para cada `Γ` y el alfabeto finito `[-B,B]^d`, los vectores de
multiplicidad no nulos de carga en `Γ` tienen un conjunto FINITO de elementos minimales
(Dickson: `WellQuasiOrderedLE (Alph → ℕ)` en Mathlib). Su mayor peso es `atomBound`. Un bloque
no vacío de cardinal mínimo con suma en `Γ` tiene multiplicidad minimal, luego cardinal
`≤ atomBound`. La uniformidad proviene de que sólo hay finitos `Γ` (subconjuntos de la caja
`[-R,R]^d`), NO de cotas de rango/torsión. No se cociente por la torsión: la condición es
pertenencia exacta a `Γ`.
-/

open Submodule Finset

noncomputable section
open Classical

namespace TypedTriangle.Grouping

open TypedTriangle.QuotientBox

/-- Alfabeto finito de fichas: la caja `[-B,B]^d`. -/
abbrev Alph (d B : ℕ) := ↥(box d B)

/-- Carga de un vector de multiplicidades. -/
def charge {d B : ℕ} (m : Alph d B → ℕ) : Fin d → ℤ :=
  ∑ a, (m a : ℤ) • (a : Fin d → ℤ)

/-- Multiplicidades no nulas con carga en `Γ`. -/
def IsZeroSum {d B : ℕ} (Γ : Submodule ℤ (Fin d → ℤ)) (m : Alph d B → ℕ) : Prop :=
  m ≠ 0 ∧ charge m ∈ Γ

/-- **Dickson.** Los minimales de `IsZeroSum Γ` forman un conjunto finito. -/
lemma minimal_finite (d B : ℕ) (Γ : Submodule ℤ (Fin d → ℤ)) :
    {m : Alph d B → ℕ | Minimal (IsZeroSum Γ) m}.Finite :=
  WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)

/-- Mayor peso de un átomo (multiplicidad minimal) para `Γ` y el alfabeto `[-B,B]^d`. -/
def atomBound (d B : ℕ) (Γ : Submodule ℤ (Fin d → ℤ)) : ℕ :=
  (minimal_finite d B Γ).toFinset.sup fun m => ∑ a, m a

/-- **Constante uniforme** `N(d,B,R)`: máximo de `atomBound` sobre los finitos retículos
generados por subconjuntos de `[-R,R]^d` (y al menos `1`). -/
def groupBound (d B R : ℕ) : ℕ :=
  max 1 ((box d R).powerset.sup fun S => atomBound d B (span ℤ (S : Set (Fin d → ℤ))))

lemma one_le_groupBound (d B R : ℕ) : 1 ≤ groupBound d B R := le_max_left _ _

lemma atomBound_le_groupBound {d B R : ℕ} {G : Set (Fin d → ℤ)}
    (hG : ∀ g ∈ G, ∀ k, |g k| ≤ R) : atomBound d B (span ℤ G) ≤ groupBound d B R := by
  have hSeq : span ℤ G = span ℤ (((box d R).filter (· ∈ G) : Finset _) : Set (Fin d → ℤ)) := by
    congr 1
    ext z; simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨mem_box.2 (hG z h), h⟩, fun h => h.2⟩
  rw [hSeq]
  have hmem : (box d R).filter (· ∈ G) ∈ (box d R).powerset :=
    Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have := Finset.le_sup
    (f := fun S : Finset (Fin d → ℤ) => atomBound d B (span ℤ (S : Set (Fin d → ℤ)))) hmem
  exact this.trans (le_max_right _ _)

section Tokens

variable {ι : Type*} [DecidableEq ι] {d B : ℕ} (z : ι → Fin d → ℤ) (hz : ∀ i k, |z i k| ≤ B)
include hz

/-- La ficha `z i` como letra del alfabeto. -/
def letter (i : ι) : Alph d B := ⟨z i, mem_box.2 (hz i)⟩

/-- Multiplicidades de un conjunto de índices. -/
def mult (J : Finset ι) : Alph d B → ℕ := fun a => #(J.filter fun i => letter z hz i = a)

omit [DecidableEq ι] in
lemma sum_eq_charge (J : Finset ι) : ∑ i ∈ J, z i = charge (mult z hz J) := by
  unfold charge mult
  rw [← Finset.sum_fiberwise J (letter z hz) z]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : ∀ i ∈ J.filter (fun i => letter z hz i = a), z i = (a : Fin d → ℤ) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [← hi.2]; rfl
  rw [Finset.sum_congr rfl h, Finset.sum_const, Nat.cast_smul_eq_nsmul]

omit [DecidableEq ι] in
lemma card_eq_sum_mult (J : Finset ι) : #J = ∑ a, mult z hz J a := by
  unfold mult
  exact Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_coe.2 (Finset.mem_univ _))

/-- Realización de una multiplicidad `m ≤ mult J` por un subconjunto `J' ⊆ J`. -/
lemma exists_sub_of_le (J : Finset ι) (m : Alph d B → ℕ) (hm : m ≤ mult z hz J) :
    ∃ J' ⊆ J, mult z hz J' = m := by
  have : ∀ a, ∃ t ⊆ J.filter (fun i => letter z hz i = a), #t = m a :=
    fun a => Finset.exists_subset_card_eq (hm a)
  choose t ht hc using this
  refine ⟨Finset.univ.biUnion t, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, -, hia⟩ := Finset.mem_biUnion.1 hi
    exact (Finset.mem_filter.1 (ht a hia)).1
  · funext a
    unfold mult
    rw [← hc a]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨b, hb⟩, rfl⟩
      have := (Finset.mem_filter.1 (ht b hb)).2
      rw [this]; exact hb
    · intro hi
      exact ⟨⟨a, hi⟩, (Finset.mem_filter.1 (ht a hi)).2⟩

/-- **Paso clave (Γ fijo).** Todo `s` no vacío con suma en `Γ` contiene un bloque no vacío de
cardinal `≤ atomBound d B Γ` con suma en `Γ`. -/
lemma exists_small_block (Γ : Submodule ℤ (Fin d → ℤ)) (s : Finset ι) (hs : s.Nonempty)
    (hsum : ∑ i ∈ s, z i ∈ Γ) :
    ∃ J ⊆ s, J.Nonempty ∧ #J ≤ atomBound d B Γ ∧ ∑ i ∈ J, z i ∈ Γ := by
  set T := s.powerset.filter fun J => J.Nonempty ∧ ∑ i ∈ J, z i ∈ Γ
  have hsT : s ∈ T := Finset.mem_filter.2 ⟨Finset.mem_powerset_self _, hs, hsum⟩
  obtain ⟨J, hJT, hJmin⟩ := Finset.exists_min_image T Finset.card ⟨s, hsT⟩
  obtain ⟨hJs, hJne, hJsum⟩ := by simpa [T] using hJT
  refine ⟨J, hJs, hJne, ?_, hJsum⟩
  have hmin : Minimal (IsZeroSum Γ) (mult z hz J) := by
    refine ⟨⟨?_, by rw [← sum_eq_charge]; exact hJsum⟩, ?_⟩
    · intro h0
      obtain ⟨i, hi⟩ := hJne
      have := congrFun h0 (letter z hz i)
      simp only [mult, Pi.zero_apply, Finset.card_eq_zero] at this
      simp only [Finset.filter_eq_empty_iff] at this
      exact this hi rfl
    · intro m ⟨hm0, hmΓ⟩ hle
      obtain ⟨J', hJ'J, hJ'm⟩ := exists_sub_of_le z hz J m hle
      have hJ'ne : J'.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        apply hm0
        rw [← hJ'm]; funext a; simp [mult]
      have hJ'T : J' ∈ T := Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (hJ'J.trans hJs),
        hJ'ne, by rw [sum_eq_charge z hz, hJ'm]; exact hmΓ⟩
      have hcard := hJmin J' hJ'T
      rw [card_eq_sum_mult z hz J, card_eq_sum_mult z hz J', hJ'm] at hcard
      have heq := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun a _ => hle a)).1
        (le_antisymm (Finset.sum_le_sum fun a _ => hle a) hcard)
      intro a; exact (heq a (Finset.mem_univ _)).ge
  rw [card_eq_sum_mult z hz J]
  exact Finset.le_sup (f := fun m : Alph d B → ℕ => ∑ a, m a)
    ((minimal_finite d B Γ).mem_toFinset.2 hmin)

/-- **Partición (Γ fijo, cota `K ≥ atomBound`).** Por inducción fuerte sobre `s`. -/
lemma exists_partition_of_bound (Γ : Submodule ℤ (Fin d → ℤ)) (K : ℕ)
    (hK : atomBound d B Γ ≤ K) (s : Finset ι) (hsum : ∑ i ∈ s, z i ∈ Γ) :
    ∃ P : Finpartition s, ∀ J ∈ P.parts, #J ≤ K ∧ ∑ i ∈ J, z i ∈ Γ := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨Finpartition.empty _, by simp [Finpartition.empty]⟩
    obtain ⟨J, hJs, hJne, hJcard, hJsum⟩ := exists_small_block z hz Γ s hs hsum
    have hlt : s \ J ⊂ s := Finset.sdiff_ssubset hJs hJne
    have hrest : ∑ i ∈ s \ J, z i ∈ Γ := by
      have := Finset.sum_sdiff hJs (f := z)
      have h' : ∑ i ∈ s \ J, z i = ∑ i ∈ s, z i - ∑ i ∈ J, z i := by rw [← this]; abel
      rw [h']; exact sub_mem hsum hJsum
    obtain ⟨P', hP'⟩ := ih (s \ J) hlt hrest
    refine ⟨P'.extend (b := J) (Finset.nonempty_iff_ne_empty.1 hJne)
      Finset.sdiff_disjoint (Finset.sdiff_union_of_subset hJs), ?_⟩
    intro K' hK'
    rw [Finpartition.extend_parts, Finset.mem_insert] at hK'
    rcases hK' with rfl | hK'
    · exact ⟨hJcard.trans hK, hJsum⟩
    · exact hP' K' hK'

end Tokens

/-- **Teorema de agrupación uniforme (S26 §6), forma `Finpartition`.**
`N = groupBound d B R` depende sólo de `d, B, R`. Para cualquier tipo finito de índices,
cualquier `Γ = span G` con `G ⊆ [-R,R]^d` y fichas `z i ∈ [-B,B]^d` con `∑ z i ∈ Γ`, existe una
partición finita de TODOS los índices en bloques de cardinal `≤ N` con suma en `Γ`. -/
theorem uniform_grouping {ι : Type*} [Fintype ι] [DecidableEq ι] (d B R : ℕ)
    (Γ : Submodule ℤ (Fin d → ℤ)) (G : Set (Fin d → ℤ)) (hΓ : Γ = span ℤ G)
    (hG : ∀ g ∈ G, ∀ k, |g k| ≤ R) (z : ι → Fin d → ℤ) (hz : ∀ i k, |z i k| ≤ B)
    (hsum : ∑ i, z i ∈ Γ) :
    ∃ P : Finpartition (Finset.univ : Finset ι),
      ∀ J ∈ P.parts, #J ≤ groupBound d B R ∧ ∑ i ∈ J, z i ∈ Γ := by
  subst hΓ
  exact exists_partition_of_bound z hz _ _ (atomBound_le_groupBound hG) _ hsum

/-- **Teorema de agrupación uniforme, forma explícita.** Con `N := groupBound d B R ≥ 1`
fijado antes de `Γ`, `ι` y `z`: una familia finita `P` de bloques de índices, no vacíos,
disjuntos dos a dos, de cardinal `≤ N`, con suma en `Γ`, y tal que cada índice pertenece a
EXACTAMENTE un bloque. -/
theorem uniform_grouping_explicit (d B R : ℕ) :
    1 ≤ groupBound d B R ∧
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Submodule ℤ (Fin d → ℤ)) (G : Set (Fin d → ℤ)),
      Γ = span ℤ G → (∀ g ∈ G, ∀ k, |g k| ≤ R) →
      ∀ z : ι → Fin d → ℤ, (∀ i k, |z i k| ≤ B) → ∑ i, z i ∈ Γ →
      ∃ P : Finset (Finset ι),
        (∀ J ∈ P, J.Nonempty) ∧
        (P : Set (Finset ι)).PairwiseDisjoint id ∧
        (∀ i, ∃! J, J ∈ P ∧ i ∈ J) ∧
        (∀ J ∈ P, #J ≤ groupBound d B R) ∧
        (∀ J ∈ P, ∑ i ∈ J, z i ∈ Γ) := by
  refine ⟨one_le_groupBound d B R, ?_⟩
  intro ι _ _ Γ G hΓ hG z hz hsum
  obtain ⟨P, hP⟩ := uniform_grouping d B R Γ G hΓ hG z hz hsum
  refine ⟨P.parts, fun J hJ => P.nonempty_of_mem_parts hJ, P.disjoint,
    fun i => P.existsUnique_mem (Finset.mem_univ i), fun J hJ => (hP J hJ).1,
    fun J hJ => (hP J hJ).2⟩

/-- **Forma existencial** `∃ N ≥ 1` cuantificada ANTES del retículo y de las fichas
(universo de índices fijo `u`). -/
theorem exists_uniform_grouping_bound (d B R : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Submodule ℤ (Fin d → ℤ)) (G : Set (Fin d → ℤ)),
      Γ = span ℤ G → (∀ g ∈ G, ∀ k, |g k| ≤ R) →
      ∀ z : ι → Fin d → ℤ, (∀ i k, |z i k| ≤ B) → ∑ i, z i ∈ Γ →
      ∃ P : Finset (Finset ι),
        (∀ J ∈ P, J.Nonempty) ∧
        (P : Set (Finset ι)).PairwiseDisjoint id ∧
        (∀ i, ∃! J, J ∈ P ∧ i ∈ J) ∧
        (∀ J ∈ P, #J ≤ N) ∧
        (∀ J ∈ P, ∑ i ∈ J, z i ∈ Γ) :=
  ⟨groupBound d B R, uniform_grouping_explicit d B R⟩

/-- Caso del conjunto vacío de fichas: la única partición es vacía. -/
example (d B R : ℕ) (Γ : Submodule ℤ (Fin d → ℤ)) (G : Set (Fin d → ℤ)) (hΓ : Γ = span ℤ G)
    (hG : ∀ g ∈ G, ∀ k, |g k| ≤ R) (z : Empty → Fin d → ℤ) :
    ∃ P : Finpartition (Finset.univ : Finset Empty),
      ∀ J ∈ P.parts, #J ≤ groupBound d B R ∧ ∑ i ∈ J, z i ∈ Γ :=
  uniform_grouping d B R Γ G hΓ hG z (fun i => i.elim) (by simp)

/-- Caso `d = 0`: toda familia finita se agrupa (bloques de cardinal `≤ groupBound 0 B R`). -/
example (B R : ℕ) {ι : Type*} [Fintype ι] (z : ι → Fin 0 → ℤ) :
    ∃ P : Finpartition (Finset.univ : Finset ι),
      ∀ J ∈ P.parts, #J ≤ groupBound 0 B R ∧ ∑ i ∈ J, z i ∈ (⊥ : Submodule ℤ (Fin 0 → ℤ)) :=
  uniform_grouping 0 B R ⊥ ∅ (by simp) (by simp) z (fun _ k => k.elim0)
    (by rw [Submodule.mem_bot]; funext k; exact k.elim0)

end TypedTriangle.Grouping
