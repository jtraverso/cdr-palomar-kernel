/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.TupleCount

@[expose] public section

/-!
# G1-Z, §4 de la guía V6 — Lema muestral de prefijo y bloque final para una componente

Marco: un grafo `J` sobre `Ω` (`N = |Ω|`), una componente `K` (no vacía, cerrada) de grado
mínimo `≥ cN` y con **expansión de vértices** `ExpandOn J K c κ` (la salida de
`expansion_of_robust`).

Muestra: un prefijo `p : Fin L → Fin Q → Ω` (`L` bloques de `Q` valores) y un bloque final
`f : Fin b → Ω`, todos con reemplazo. El proceso de crecimiento es determinista en función del
prefijo: `Cs p j` es un conjunto conexo de valores ya expuestos; en el bloque `j` se añade un
valor del conjunto bueno `goodSet (Cs p j)` (cualquier punto de `K` si `C = ∅`; si no, un punto
de `N[C]` con `≥ κηN` vecinos fuera de `N[C]`), salvo que el proceso haya terminado
(`|K ∖ N[C]| < ηN`). Los conjuntos buenos dependen del prefijo; sus fallos se cuentan con
`card_update_le`, sin suponer independencia entre pasos.

Los puntos marcados `M p` se eligen como función del PREFIJO, antes del bloque final.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence

universe u

variable {Ω : Type u} [Fintype Ω]

/-- Expansión de vértices de `K` en `J` (forma usada por el muestreo). -/
def ExpandOn (J : SimpleGraph Ω) (K : Finset Ω) (c κ : ℝ) : Prop :=
  ∀ S ⊆ K, c * Fintype.card Ω ≤ S.card → ∀ η : ℝ, 0 < η → η ≤ 1 →
    η * Fintype.card Ω ≤ (K \ S).card →
    κ * η * Fintype.card Ω ≤
      ((S.filter (fun x => κ * η * Fintype.card Ω ≤ (nbIn J (K \ S) x).card)).card : ℝ)

lemma expandOn_of_robust {J : SimpleGraph Ω} {K : Finset Ω} {c ζ ρ : ℝ} (hc : 0 < c)
    (hζ : 0 < ζ) (hζc : ζ ≤ c) (hρ : 0 < ρ) (hK : NbrClosed J K) (hdeg : MinDegOn J K c)
    (hrob : RobustConn J K ζ ρ) : ExpandOn J K c (expConst c ζ ρ) :=
  fun _ hSK hS _ hη hη1 hT => expansion_of_robust hc hζ hζc hρ hK hdeg hrob hSK hS hη hη1 hT

lemma ExpandOn.mono {J : SimpleGraph Ω} {K : Finset Ω} {c κ κ' : ℝ} (h : ExpandOn J K c κ)
    (hle : κ' ≤ κ) : ExpandOn J K c κ' := by
  intro S hSK hS η hη hη1 hT
  have h1 := h S hSK hS η hη hη1 hT
  have hle' : κ' * η * Fintype.card Ω ≤ κ * η * Fintype.card Ω := by
    have := mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ η * Fintype.card Ω)
    nlinarith
  exact hle'.trans (h1.trans (card_filter_threshold_mono S _ hle'))

lemma inducedOn_mono (G : SimpleGraph Ω) {W W' : Finset Ω} (h : W ⊆ W') :
    inducedOn G W ≤ inducedOn G W' := fun _ _ hab => ⟨hab.1, h hab.2.1, h hab.2.2⟩

namespace Sampler

variable (J : SimpleGraph Ω) (K : Finset Ω) (κ η : ℝ)

/-- Vecindad cerrada `N[C]`. -/
def NC (C : Finset Ω) : Finset Ω := C ∪ univ.filter (fun y => ∃ x ∈ C, J.Adj x y)

/-- Terminación: `C ≠ ∅` y `|K ∖ N[C]| < ηN`. -/
def Term (C : Finset Ω) : Prop := C.Nonempty ∧ ((K \ NC J C).card : ℝ) < η * Fintype.card Ω

/-- Conjunto bueno del paso. -/
def goodSet (C : Finset Ω) : Finset Ω :=
  if C = ∅ then K
  else (NC J C).filter (fun x => κ * η * Fintype.card Ω ≤ (nbIn J (K \ NC J C) x).card)

/-- Un paso del proceso de crecimiento con un bloque de valores. -/
def step {Q : ℕ} (C : Finset Ω) (blk : Fin Q → Ω) : Finset Ω :=
  if Term J K η C then C
  else if h : ∃ i, blk i ∈ goodSet J K κ η C then insert (blk h.choose) C else C

/-- Conjunto conexo tras `j` bloques. -/
def Cs {L Q : ℕ} (p : Fin L → Fin Q → Ω) : ℕ → Finset Ω
  | 0 => ∅
  | j + 1 => if h : j < L then step J K κ η (Cs p j) (p ⟨j, h⟩) else Cs p j

/-- Valores del prefijo. -/
def pvals {L Q : ℕ} (p : Fin L → Fin Q → Ω) : Finset Ω :=
  univ.image (fun ji : Fin L × Fin Q => p ji.1 ji.2)

/-- Fallo del bloque `j`: el proceso no terminó y el bloque no encontró un punto bueno. -/
def Fail {L Q : ℕ} (p : Fin L → Fin Q → Ω) (j : Fin L) : Prop :=
  ¬ Term J K η (Cs J K κ η p j) ∧ ∀ i, p j i ∉ goodSet J K κ η (Cs J K κ η p j)

variable {J K κ η}

lemma Cs_succ {L Q : ℕ} (p : Fin L → Fin Q → Ω) {j : ℕ} (h : j < L) :
    Cs J K κ η p (j + 1) = step J K κ η (Cs J K κ η p j) (p ⟨j, h⟩) := by
  simp [Cs, h]

lemma Cs_update {L Q : ℕ} (p : Fin L → Fin Q → Ω) (j : Fin L) (x : Fin Q → Ω) :
    ∀ j' ≤ j.val, Cs J K κ η (Function.update p j x) j' = Cs J K κ η p j' := by
  intro j' hj'
  induction j' with
  | zero => rfl
  | succ j' ih =>
    have hj'L : j' < L := by omega
    rw [Cs_succ _ hj'L, Cs_succ _ hj'L, ih (by omega)]
    have hne : (⟨j', hj'L⟩ : Fin L) ≠ j := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    rw [Function.update_of_ne hne]

lemma mem_NC_self {C : Finset Ω} {x : Ω} (hx : x ∈ C) : x ∈ NC J C :=
  Finset.mem_union_left _ hx

lemma NC_subset {C : Finset Ω} (hK : NbrClosed J K) (hC : C ⊆ K) : NC J C ⊆ K := by
  intro y hy
  rcases Finset.mem_union.1 hy with hy | hy
  · exact hC hy
  · obtain ⟨x, hx, hxy⟩ := (Finset.mem_filter.1 hy).2
    exact hK x (hC hx) y hxy

lemma goodSet_subset {C : Finset Ω} (hK : NbrClosed J K) (hC : C ⊆ K) :
    goodSet J K κ η C ⊆ K := by
  unfold goodSet
  split_ifs
  · exact subset_rfl
  · exact (Finset.filter_subset _ _).trans (NC_subset hK hC)

/-- Descripción de un paso. -/
lemma step_cases {Q : ℕ} (C : Finset Ω) (blk : Fin Q → Ω) :
    step J K κ η C blk = C ∨
      (¬ Term J K η C ∧ ∃ i, blk i ∈ goodSet J K κ η C ∧ step J K κ η C blk = insert (blk i) C) := by
  unfold step
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr ⟨h1, h2.choose, h2.choose_spec, rfl⟩
  · exact Or.inl rfl

lemma Cs_subset_K {L Q : ℕ} (hK : NbrClosed J K) (p : Fin L → Fin Q → Ω) :
    ∀ j, Cs J K κ η p j ⊆ K := by
  intro j
  induction j with
  | zero => simp [Cs]
  | succ j ih =>
    by_cases h : j < L
    · rw [Cs_succ _ h]
      rcases step_cases (J := J) (K := K) (κ := κ) (η := η) (Cs J K κ η p j) (p ⟨j, h⟩) with
        e | ⟨-, i, hi, e⟩
      · rw [e]; exact ih
      · rw [e]; exact Finset.insert_subset (goodSet_subset hK ih hi) ih
    · simp only [Cs, h, dite_false]; exact ih

lemma Cs_subset_pvals {L Q : ℕ} (p : Fin L → Fin Q → Ω) :
    ∀ j, Cs J K κ η p j ⊆ pvals p := by
  intro j
  induction j with
  | zero => simp [Cs]
  | succ j ih =>
    by_cases h : j < L
    · rw [Cs_succ _ h]
      rcases step_cases (J := J) (K := K) (κ := κ) (η := η) (Cs J K κ η p j) (p ⟨j, h⟩) with
        e | ⟨-, i, -, e⟩
      · rw [e]; exact ih
      · rw [e]
        refine Finset.insert_subset ?_ ih
        exact Finset.mem_image.2 ⟨(⟨j, h⟩, i), Finset.mem_univ _, rfl⟩
    · simp only [Cs, h, dite_false]; exact ih

/-- El conjunto del proceso es conexo en su propio inducido. -/
lemma Cs_conn {L Q : ℕ} (p : Fin L → Fin Q → Ω) :
    ∀ j, ∀ x ∈ Cs J K κ η p j, ∀ y ∈ Cs J K κ η p j,
      (inducedOn J (Cs J K κ η p j)).Reachable x y := by
  intro j
  induction j with
  | zero => simp [Cs]
  | succ j ih =>
    by_cases h : j < L
    · rw [Cs_succ _ h]
      set C := Cs J K κ η p j
      rcases step_cases (J := J) (K := K) (κ := κ) (η := η) C (p ⟨j, h⟩) with e | ⟨-, i, hi, e⟩
      · rw [e]; exact ih
      · rw [e]
        set z := p ⟨j, h⟩ i
        have hmono := inducedOn_mono J (Finset.subset_insert z C)
        -- `z` está conectado a `C` (o `C = ∅`)
        have hz : C = ∅ ∨ ∃ c ∈ C, (inducedOn J (insert z C)).Reachable z c := by
          by_cases hC : C = ∅
          · exact Or.inl hC
          · right
            have hi' : z ∈ NC J C := by
              simp only [goodSet, hC, if_false] at hi
              exact (Finset.mem_filter.1 hi).1
            rcases Finset.mem_union.1 hi' with hzC | hzN
            · exact ⟨z, hzC, SimpleGraph.Reachable.refl _⟩
            · obtain ⟨c, hc, hcz⟩ := (Finset.mem_filter.1 hzN).2
              exact ⟨c, hc, (SimpleGraph.Adj.reachable
                ⟨hcz.symm, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hc⟩)⟩
        have hall : ∀ x ∈ insert z C, ∀ y ∈ insert z C,
            (inducedOn J (insert z C)).Reachable x y := by
          rcases hz with hC | ⟨c, hc, hzc⟩
          · intro x hx y hy
            rw [hC] at hx hy
            simp only [insert_empty, Finset.mem_singleton] at hx hy
            subst hx; subst hy; exact SimpleGraph.Reachable.refl _
          · have hC' : ∀ x ∈ insert z C, (inducedOn J (insert z C)).Reachable x c := by
              intro x hx
              rcases Finset.mem_insert.1 hx with rfl | hx
              · exact hzc
              · exact (ih x hx c hc).mono hmono
            intro x hx y hy
            exact (hC' x hx).trans (hC' y hy).symm
        exact hall
    · simp only [Cs, h, dite_false]; exact ih

/-- La terminación es estable. -/
lemma Cs_stable {L Q : ℕ} (p : Fin L → Fin Q → Ω) {j : ℕ} (hT : Term J K η (Cs J K κ η p j)) :
    ∀ k, j ≤ k → Cs J K κ η p k = Cs J K κ η p j := by
  intro k hk
  induction k with
  | zero => have : j = 0 := by omega
            subst this; rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hk with e | hlt
    · rw [e]
    · have ih' := ih (by omega)
      by_cases h : k < L
      · rw [Cs_succ _ h, ih']
        unfold step; rw [if_pos hT]
      · simp only [Cs, h, dite_false]; exact ih'

lemma NC_mono {C C' : Finset Ω} (h : C ⊆ C') : NC J C ⊆ NC J C' := by
  intro y hy
  rcases Finset.mem_union.1 hy with hy | hy
  · exact Finset.mem_union_left _ (h hy)
  · obtain ⟨x, hx, hxy⟩ := (Finset.mem_filter.1 hy).2
    exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, x, h hx, hxy⟩)

lemma nbrs_subset_NC {C : Finset Ω} {x : Ω} (hx : x ∈ C) : univ.filter (J.Adj x) ⊆ NC J C :=
  fun _ hy => Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx,
    (Finset.mem_filter.1 hy).2⟩)

lemma card_le_N (A : Finset Ω) : (A.card : ℝ) ≤ Fintype.card Ω := by
  exact_mod_cast Finset.card_le_univ A

/-- Crecimiento de `N[C]` en un paso exitoso. -/
lemma growth {c : ℝ} (hdeg : MinDegOn J K c) (hκηc : κ * η ≤ c) {C : Finset Ω}
    {x : Ω} (hx : x ∈ goodSet J K κ η C) :
    ((NC J C).card : ℝ) + κ * η * Fintype.card Ω ≤ (NC J (insert x C)).card := by
  have hN : (0 : ℝ) ≤ Fintype.card Ω := by positivity
  by_cases hC : C = ∅
  · subst hC
    simp only [goodSet, if_true] at hx
    have h0 : NC J (∅ : Finset Ω) = ∅ := by ext; simp [NC]
    rw [h0, Finset.card_empty, Nat.cast_zero, zero_add]
    have h1 := hdeg x hx
    have h2 : ((univ.filter (J.Adj x)).card : ℝ) ≤ (NC J (insert x ∅)).card := by
      exact_mod_cast Finset.card_le_card (nbrs_subset_NC (Finset.mem_insert_self x ∅))
    have : κ * η * Fintype.card Ω ≤ c * Fintype.card Ω := mul_le_mul_of_nonneg_right hκηc hN
    linarith
  · simp only [goodSet, hC, if_false] at hx
    obtain ⟨hxN, hxdeg⟩ := Finset.mem_filter.1 hx
    have hdisj : Disjoint (NC J C) (nbIn J (K \ NC J C) x) := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 hy').1).2 hy
    have hsub : NC J C ∪ nbIn J (K \ NC J C) x ⊆ NC J (insert x C) := by
      refine Finset.union_subset (NC_mono (Finset.subset_insert x C)) fun y hy => ?_
      exact nbrs_subset_NC (Finset.mem_insert_self x C)
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hy).2⟩)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at h1
    have : ((NC J C).card : ℝ) + (nbIn J (K \ NC J C) x).card ≤ (NC J (insert x C)).card := by
      exact_mod_cast h1
    linarith

/-- El conjunto bueno es grande mientras el proceso no termina. -/
lemma goodSet_card {c : ℝ} (hK : NbrClosed J K) (hdeg : MinDegOn J K c)
    (hexp : ExpandOn J K c κ) (hne : K.Nonempty) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hκηc : κ * η ≤ c) {C : Finset Ω} (hC : C ⊆ K) (hnt : ¬ Term J K η C) :
    κ * η * Fintype.card Ω ≤ (goodSet J K κ η C).card := by
  have hN : (0 : ℝ) ≤ Fintype.card Ω := by positivity
  by_cases hC0 : C = ∅
  · simp only [goodSet, hC0, if_true]
    obtain ⟨a, ha⟩ := hne
    have h1 := hdeg a ha
    have h2 : ((univ.filter (J.Adj a)).card : ℝ) ≤ K.card := by
      exact_mod_cast Finset.card_le_card fun y hy => hK a ha y (Finset.mem_filter.1 hy).2
    have : κ * η * Fintype.card Ω ≤ c * Fintype.card Ω := mul_le_mul_of_nonneg_right hκηc hN
    linarith
  · simp only [goodSet, hC0, if_false]
    obtain ⟨c0, hc0⟩ := Finset.nonempty_iff_ne_empty.2 hC0
    have hT : η * Fintype.card Ω ≤ (K \ NC J C).card := by
      by_contra h; push_neg at h
      exact hnt ⟨⟨c0, hc0⟩, h⟩
    have hS : c * Fintype.card Ω ≤ (NC J C).card := by
      have h1 := hdeg c0 (hC hc0)
      have h2 : ((univ.filter (J.Adj c0)).card : ℝ) ≤ (NC J C).card := by
        exact_mod_cast Finset.card_le_card (nbrs_subset_NC hc0)
      linarith
    exact hexp _ (NC_subset hK hC) hS η hη0 hη1 hT

/-- **Terminación del prefijo.** Si ningún bloque falla y `LκηN > N`, el proceso termina. -/
lemma terminates {c : ℝ} {L Q : ℕ} (hdeg : MinDegOn J K c) (hκηc : κ * η ≤ c)
    (p : Fin L → Fin Q → Ω) (hnf : ∀ j, ¬ Fail J K κ η p j)
    (hL : (Fintype.card Ω : ℝ) < L * (κ * η * Fintype.card Ω)) :
    Term J K η (Cs J K κ η p L) := by
  by_contra hT
  have hnt : ∀ j ≤ L, ¬ Term J K η (Cs J K κ η p j) := by
    intro j hj hTj
    exact hT (Cs_stable p hTj L hj ▸ hTj)
  have hgrow : ∀ j ≤ L, (j : ℝ) * (κ * η * Fintype.card Ω) ≤ (NC J (Cs J K κ η p j)).card := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hjL : j < L := by omega
      have ih' := ih (by omega)
      have hntj := hnt j (by omega)
      have hex : ∃ i, p ⟨j, hjL⟩ i ∈ goodSet J K κ η (Cs J K κ η p j) := by
        by_contra hno
        push_neg at hno
        exact hnf ⟨j, hjL⟩ ⟨hntj, hno⟩
      rw [Cs_succ _ hjL]
      unfold step
      rw [if_neg hntj, dif_pos hex]
      have := growth hdeg hκηc hex.choose_spec
      push_cast
      linarith
  have h1 := hgrow L le_rfl
  have h2 := card_le_N (NC J (Cs J K κ η p L))
  linarith

/-- **Conteo de los fallos de un bloque.** -/
lemma card_fail_le {c : ℝ} {L Q : ℕ} (hK : NbrClosed J K) (hdeg : MinDegOn J K c)
    (hexp : ExpandOn J K c κ) (hne : K.Nonempty) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hκηc : κ * η ≤ c) (hκη1 : κ * η ≤ 1) (j : Fin L) :
    ((univ.filter (fun p : Fin L → Fin Q → Ω => Fail J K κ η p j)).card : ℝ) ≤
      (1 - κ * η) ^ Q * Fintype.card (Fin L → Fin Q → Ω) := by
  refine card_le_of_update j _ fun p => ?_
  set C := Cs J K κ η p j
  by_cases hT : Term J K η C
  · refine ⟨∅, fun x hx => ?_, by
      simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (pow_nonneg (by linarith) _) (by positivity)⟩
    have hF := (Finset.mem_filter.1 hx).2
    have e : Cs J K κ η (Function.update p j x) j = C := Cs_update p j x j le_rfl
    exact absurd (e ▸ hF.1) (not_not.2 hT)
  · refine ⟨univ.filter (fun x : Fin Q → Ω => ∀ i, x i ∉ goodSet J K κ η C), fun x hx => ?_, ?_⟩
    · have hF := (Finset.mem_filter.1 hx).2
      have e : Cs J K κ η (Function.update p j x) j = C := Cs_update p j x j le_rfl
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i => ?_⟩
      have := hF.2 i
      rw [e, Function.update_self] at this
      exact this
    · rw [card_tuples_avoid]
      have hG := goodSet_card hK hdeg hexp hne hη0 hη1 hκηc (Cs_subset_K hK p j) hT
      have hGN : (goodSet J K κ η C).card ≤ Fintype.card Ω := Finset.card_le_univ _
      have hcast : ((Fintype.card Ω - (goodSet J K κ η C).card : ℕ) : ℝ) ≤
          (1 - κ * η) * Fintype.card Ω := by
        rw [Nat.cast_sub hGN]; linarith
      have hpow := pow_le_pow_left₀ (by positivity) hcast Q
      rw [Fintype.card_fun, Fintype.card_fin]
      push_cast
      rw [mul_pow] at hpow
      exact hpow

/-- Valores del bloque final. -/
def fvals {b : ℕ} (f : Fin b → Ω) : Finset Ω := univ.image f

variable (J K κ η) in
/-- Objetivos del bloque final: valores del prefijo y marcados, en `K`. -/
def targets {L Q : ℕ} (p : Fin L → Fin Q → Ω) (M : Finset Ω) : Finset Ω :=
  (pvals p ∪ M).filter (· ∈ K)

variable (J K κ η) in
/-- Fallo del bloque final para un prefijo `p`. -/
def BadF {L Q b : ℕ} (p : Fin L → Fin Q → Ω) (M : Finset Ω) (f : Fin b → Ω) : Prop :=
  (∃ y ∈ targets K p M, ∀ i, f i ∉ nbIn J (NC J (Cs J K κ η p L)) y) ∨
    (∃ i, f i ∈ K \ NC J (Cs J K κ η p L))

end Sampler

open Sampler

/-- Suceso bueno de la muestra para la componente `K` con marcados `M`: el prefijo toca `K`
y todos los valores (y marcados) en `K` están conectados en el inducido sobre valores y
marcados. -/
def SampleGood [DecidableEq Ω] (J : SimpleGraph Ω) (K M pv vals : Finset Ω) : Prop :=
  (∃ x ∈ pv, x ∈ K) ∧ ∀ x ∈ vals ∪ M, x ∈ K → ∀ y ∈ vals ∪ M, y ∈ K →
    (inducedOn J (vals ∪ M)).Reachable x y

namespace Sampler

variable {J K κ η}

/-- **El suceso bueno, de forma determinista.** -/
lemma sampleGood_of {L Q b : ℕ} (hK : NbrClosed J K) (p : Fin L → Fin Q → Ω) (M : Finset Ω)
    (f : Fin b → Ω) (hT : Term J K η (Cs J K κ η p L)) (hbad : ¬ BadF J K κ η p M f) :
    SampleGood J K M (pvals p) (pvals p ∪ fvals f) := by
  set C := Cs J K κ η p L
  set S := NC J C
  set A := (pvals p ∪ fvals f) ∪ M
  obtain ⟨c0, hc0⟩ := hT.1
  have hCK : C ⊆ K := Cs_subset_K hK p L
  have hCpv : C ⊆ pvals p := Cs_subset_pvals p L
  have hCA : C ⊆ A := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (hCpv hx))
  have hmono := inducedOn_mono J hCA
  have hCc : ∀ x ∈ C, (inducedOn J A).Reachable x c0 := fun x hx =>
    (Cs_conn p L x hx c0 hc0).mono hmono
  simp only [BadF, not_or, not_exists, not_and, not_forall, not_not] at hbad
  obtain ⟨hb1, hb2⟩ := hbad
  -- un valor final en `S` se conecta a `c0`
  have hS : ∀ z ∈ A, z ∈ S → (inducedOn J A).Reachable z c0 := by
    intro z hzA hzS
    rcases Finset.mem_union.1 hzS with hzC | hzN
    · exact hCc z hzC
    · obtain ⟨x, hxC, hxz⟩ := (Finset.mem_filter.1 hzN).2
      exact (show (inducedOn J A).Adj z x from ⟨hxz.symm, hzA, hCA hxC⟩).reachable.trans
        (hCc x hxC)
  have hfA : ∀ i, f i ∈ A := fun i => Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
  have hall : ∀ x ∈ A, x ∈ K → (inducedOn J A).Reachable x c0 := by
    intro x hxA hxK
    by_cases hxf : x ∈ fvals f
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hxf
      have : f i ∈ S := by
        by_contra hn
        exact hb2 i (Finset.mem_sdiff.2 ⟨hxK, hn⟩)
      exact hS _ (hfA i) this
    · have hxT : x ∈ targets K p M := by
        refine Finset.mem_filter.2 ⟨?_, hxK⟩
        rcases Finset.mem_union.1 hxA with h1 | h1
        · rcases Finset.mem_union.1 h1 with h2 | h2
          · exact Finset.mem_union_left _ h2
          · exact absurd h2 hxf
        · exact Finset.mem_union_right _ h1
      obtain ⟨i, hi⟩ := hb1 x hxT
      obtain ⟨hiS, hadj⟩ := Finset.mem_filter.1 hi
      exact (show (inducedOn J A).Adj x (f i) from ⟨hadj, hxA, hfA i⟩).reachable.trans
        (hS _ (hfA i) hiS)
  refine ⟨⟨c0, hCpv hc0, hCK hc0⟩, fun x hx hxK y hy hyK => ?_⟩
  exact (hall x hx hxK).trans (hall y hy hyK).symm

lemma card_pvals_le {L Q : ℕ} (p : Fin L → Fin Q → Ω) : (pvals p).card ≤ L * Q := by
  refine Finset.card_image_le.trans ?_
  simp

/-- **Conteo del bloque final.** -/
lemma card_badF_le {c : ℝ} {L Q b : ℕ} (hK : NbrClosed J K) (hdeg : MinDegOn J K c)
    (hη0 : 0 ≤ η) (p : Fin L → Fin Q → Ω) (M : Finset Ω)
    (hT : Term J K η (Cs J K κ η p L)) :
    ((univ.filter (fun f : Fin b → Ω => BadF J K κ η p M f)).card : ℝ) ≤
      ((targets K p M).card * (1 - c + η) ^ b + b * η) * Fintype.card (Fin b → Ω) := by
  set S := NC J (Cs J K κ η p L)
  set N : ℝ := (Fintype.card Ω : ℝ)
  have hKS : ((K \ S).card : ℝ) < η * N := hT.2
  have hFb : (Fintype.card (Fin b → Ω) : ℝ) = N ^ b := by
    rw [Fintype.card_fun, Fintype.card_fin]; push_cast; rfl
  -- primera parte
  have hsub1 : univ.filter (fun f : Fin b → Ω => ∃ y ∈ targets K p M, ∀ i, f i ∉ nbIn J S y) ⊆
      (targets K p M).biUnion (fun y => univ.filter (fun f : Fin b → Ω => ∀ i, f i ∉ nbIn J S y)) := by
    intro f hf
    obtain ⟨y, hy, hfy⟩ := (Finset.mem_filter.1 hf).2
    exact Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_filter.2 ⟨Finset.mem_univ _, hfy⟩⟩
  have hper : ∀ y ∈ targets K p M,
      (((univ.filter (fun f : Fin b → Ω => ∀ i, f i ∉ nbIn J S y)).card : ℕ) : ℝ) ≤
        ((1 - c + η) * N) ^ b := by
    intro y hy
    have hyK := (Finset.mem_filter.1 hy).2
    rw [card_tuples_avoid]
    have hsub : univ.filter (J.Adj y) ⊆ nbIn J S y ∪ (K \ S) := by
      intro z hz
      have hz' := (Finset.mem_filter.1 hz).2
      by_cases hzS : z ∈ S
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hzS, hz'⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hK y hyK z hz', hzS⟩)
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 := hdeg y hyK
    have h3 : ((univ.filter (J.Adj y)).card : ℝ) ≤ (nbIn J S y).card + (K \ S).card := by
      exact_mod_cast h1
    have hle : (nbIn J S y).card ≤ Fintype.card Ω := Finset.card_le_univ _
    have hcast : ((Fintype.card Ω - (nbIn J S y).card : ℕ) : ℝ) ≤ (1 - c + η) * N := by
      rw [Nat.cast_sub hle]
      simp only [N] at *
      nlinarith
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcast b
  have hpart1 : ((univ.filter (fun f : Fin b → Ω =>
      ∃ y ∈ targets K p M, ∀ i, f i ∉ nbIn J S y)).card : ℝ) ≤
        (targets K p M).card * ((1 - c + η) * N) ^ b := by
    have h1 := (Finset.card_le_card hsub1).trans Finset.card_biUnion_le
    calc ((univ.filter (fun f : Fin b → Ω =>
          ∃ y ∈ targets K p M, ∀ i, f i ∉ nbIn J S y)).card : ℝ)
        ≤ ∑ y ∈ targets K p M,
            (((univ.filter (fun f : Fin b → Ω => ∀ i, f i ∉ nbIn J S y)).card : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ ≤ ∑ _y ∈ targets K p M, ((1 - c + η) * N) ^ b := Finset.sum_le_sum hper
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  -- segunda parte
  have hpart2 : ((univ.filter (fun f : Fin b → Ω => ∃ i, f i ∈ K \ S)).card : ℝ) ≤
      b * η * N ^ b := by
    have h := card_tuples_hit_le b (K \ S)
    rw [hFb] at h
    by_cases hN : N = 0
    · have : (K \ S).card = 0 := by
        have := card_le_N (K \ S); simp only [N] at hN; rw [hN] at this
        exact_mod_cast le_antisymm this (by positivity)
      refine h.trans ?_
      simp [this]
      positivity
    · have hNpos : 0 < N := lt_of_le_of_ne (by positivity) (Ne.symm hN)
      refine h.trans ?_
      have : ((K \ S).card : ℝ) / N ≤ η := by rw [div_le_iff₀ hNpos]; linarith
      have hb : (0 : ℝ) ≤ b := by positivity
      have hNb : (0 : ℝ) ≤ N ^ b := by positivity
      calc (b : ℝ) * (((K \ S).card : ℝ) / N) * N ^ b ≤ b * η * N ^ b := by gcongr
        _ = b * η * N ^ b := rfl
  have hsplit : univ.filter (fun f : Fin b → Ω => BadF J K κ η p M f) ⊆
      univ.filter (fun f : Fin b → Ω => ∃ y ∈ targets K p M, ∀ i, f i ∉ nbIn J S y) ∪
        univ.filter (fun f : Fin b → Ω => ∃ i, f i ∈ K \ S) := by
    intro f hf
    rcases (Finset.mem_filter.1 hf).2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have h1 := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  have h1' : ((univ.filter (fun f : Fin b → Ω => BadF J K κ η p M f)).card : ℝ) ≤
      ((univ.filter (fun f : Fin b → Ω => ∃ y ∈ targets K p M, ∀ i, f i ∉ nbIn J S y)).card : ℝ) +
        ((univ.filter (fun f : Fin b → Ω => ∃ i, f i ∈ K \ S)).card : ℝ) := by
    exact_mod_cast h1
  rw [hFb]
  have : (targets K p M).card * ((1 - c + η) * N) ^ b =
      (targets K p M).card * (1 - c + η) ^ b * N ^ b := by rw [mul_pow]; ring
  nlinarith

end Sampler

/-- **Lema muestral de una componente (conteo).** Con un prefijo de `L` bloques de `Q`
valores y un bloque final de `b` valores, la fracción de muestras en las que falla el suceso
bueno es a lo sumo `L(1−κη)^Q + (LQ+q)(1−c+η)^b + bη`. Los marcados `M p` dependen sólo del
prefijo. -/
theorem card_not_sampleGood_le {J : SimpleGraph Ω} {K : Finset Ω} {c κ η : ℝ} {L Q b q : ℕ}
    (hK : NbrClosed J K) (hdeg : MinDegOn J K c) (hexp : ExpandOn J K c κ) (hne : K.Nonempty)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hκηc : κ * η ≤ c) (hκη1 : κ * η ≤ 1)
    (hL : 1 < L * (κ * η)) (M : (Fin L → Fin Q → Ω) → Finset Ω) (hMq : ∀ p, (M p).card ≤ q) :
    ((univ.filter (fun x : (Fin L → Fin Q → Ω) × (Fin b → Ω) =>
      ¬ SampleGood J K (M x.1) (pvals x.1) (pvals x.1 ∪ fvals x.2))).card : ℝ) ≤
      (L * (1 - κ * η) ^ Q + (L * Q + q) * (1 - c + η) ^ b + b * η) *
        Fintype.card ((Fin L → Fin Q → Ω) × (Fin b → Ω)) := by
  set N : ℝ := (Fintype.card Ω : ℝ)
  have hNpos : 0 < N := by
    obtain ⟨a, _⟩ := hne
    have : 0 < Fintype.card Ω := Fintype.card_pos_iff.2 ⟨a⟩
    show (0 : ℝ) < (Fintype.card Ω : ℝ)
    exact_mod_cast this
  have hLN : N < L * (κ * η * N) := by nlinarith
  set A1 := univ.filter (fun x : (Fin L → Fin Q → Ω) × (Fin b → Ω) => ∃ j, Fail J K κ η x.1 j)
  set A2 := univ.filter (fun x : (Fin L → Fin Q → Ω) × (Fin b → Ω) => (∀ j, ¬ Fail J K κ η x.1 j) ∧ BadF J K κ η x.1 (M x.1) x.2)
  have hsub : univ.filter (fun x : (Fin L → Fin Q → Ω) × (Fin b → Ω) =>
      ¬ SampleGood J K (M x.1) (pvals x.1) (pvals x.1 ∪ fvals x.2)) ⊆ A1 ∪ A2 := by
    intro x hx
    have hng := (Finset.mem_filter.1 hx).2
    by_cases hf : ∃ j, Fail J K κ η x.1 j
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hf⟩)
    · push_neg at hf
      have hT := terminates hdeg hκηc x.1 hf hLN
      have hbad : BadF J K κ η x.1 (M x.1) x.2 := by
        by_contra hb
        exact hng (sampleGood_of hK x.1 (M x.1) x.2 hT hb)
      exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hf, hbad⟩)
  -- primera parte: fallos del prefijo
  have hA1 : (A1.card : ℝ) ≤ L * (1 - κ * η) ^ Q * Fintype.card (Fin L → Fin Q → Ω) * Fintype.card (Fin b → Ω) := by
    have e : A1.card = (univ.filter (fun p : (Fin L → Fin Q → Ω) => ∃ j, Fail J K κ η p j)).card *
        Fintype.card (Fin b → Ω) := by
      convert card_filter_fst (β := Fin b → Ω) (fun p : (Fin L → Fin Q → Ω) => ∃ j, Fail J K κ η p j)
    have hsubP : univ.filter (fun p : (Fin L → Fin Q → Ω) => ∃ j, Fail J K κ η p j) ⊆
        univ.biUnion (fun j : Fin L => univ.filter (fun p : (Fin L → Fin Q → Ω) => Fail J K κ η p j)) := by
      intro p hp
      obtain ⟨j, hj⟩ := (Finset.mem_filter.1 hp).2
      exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩
    have h1 := (Finset.card_le_card hsubP).trans Finset.card_biUnion_le
    have h2 : ((univ.filter (fun p : (Fin L → Fin Q → Ω) => ∃ j, Fail J K κ η p j)).card : ℝ) ≤
        L * ((1 - κ * η) ^ Q * Fintype.card (Fin L → Fin Q → Ω)) := by
      calc ((univ.filter (fun p : (Fin L → Fin Q → Ω) => ∃ j, Fail J K κ η p j)).card : ℝ)
          ≤ ∑ j : Fin L, ((univ.filter (fun p : (Fin L → Fin Q → Ω) => Fail J K κ η p j)).card : ℝ) := by
            exact_mod_cast h1
        _ ≤ ∑ _j : Fin L, (1 - κ * η) ^ Q * Fintype.card (Fin L → Fin Q → Ω) :=
            Finset.sum_le_sum fun j _ =>
              card_fail_le hK hdeg hexp hne hη0 hη1 hκηc hκη1 j
        _ = L * ((1 - κ * η) ^ Q * Fintype.card (Fin L → Fin Q → Ω)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [e]; push_cast
    have : (0 : ℝ) ≤ Fintype.card (Fin b → Ω) := by positivity
    nlinarith
  -- segunda parte: fallos del bloque final
  have hA2 : (A2.card : ℝ) ≤ ((L * Q + q) * (1 - c + η) ^ b + b * η) *
      Fintype.card (Fin L → Fin Q → Ω) * Fintype.card (Fin b → Ω) := by
    have e : A2.card = ∑ p : (Fin L → Fin Q → Ω), (univ.filter (fun f : (Fin b → Ω) =>
        (∀ j, ¬ Fail J K κ η p j) ∧ BadF J K κ η p (M p) f)).card :=
      by convert card_filter_prod (fun p f => (∀ j, ¬ Fail J K κ η p j) ∧ BadF J K κ η p (M p) f)
    have hper : ∀ p : (Fin L → Fin Q → Ω), ((univ.filter (fun f : (Fin b → Ω) =>
        (∀ j, ¬ Fail J K κ η p j) ∧ BadF J K κ η p (M p) f)).card : ℝ) ≤
          ((L * Q + q) * (1 - c + η) ^ b + b * η) * Fintype.card (Fin b → Ω) := by
      intro p
      have hc0 : 0 ≤ 1 - c + η := by
        have := hdeg
        by_contra hneg; push_neg at hneg
        -- `c ≤ 1` se deduce del grado mínimo en un `K` no vacío
        obtain ⟨a, ha⟩ := hne
        have h1 := hdeg a ha
        have h2 := card_le_N (univ.filter (J.Adj a))
        have : c * N ≤ N := h1.trans h2
        nlinarith
      by_cases hf : ∀ j, ¬ Fail J K κ η p j
      · have hT := terminates hdeg hκηc p hf hLN
        have h1 := card_badF_le (b := b) hK hdeg hη0.le p (M p) hT
        have htg : ((targets K p (M p)).card : ℝ) ≤ L * Q + q := by
          have : (targets K p (M p)).card ≤ L * Q + q :=
            (Finset.card_filter_le _ _).trans ((Finset.card_union_le _ _).trans
              (Nat.add_le_add (card_pvals_le p) (hMq p)))
          exact_mod_cast this
        refine le_trans ?_ (h1.trans ?_)
        · exact_mod_cast Finset.card_le_card fun f hf' => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf' ⊢; exact hf'.2
        · have : (0 : ℝ) ≤ (1 - c + η) ^ b := pow_nonneg hc0 b
          have : (0 : ℝ) ≤ Fintype.card (Fin b → Ω) := by positivity
          gcongr
      · have : univ.filter (fun f : (Fin b → Ω) =>
            (∀ j, ¬ Fail J K κ η p j) ∧ BadF J K κ η p (M p) f) = ∅ := by
          ext f; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_and]; intro h; exact absurd h hf
        rw [this, Finset.card_empty, Nat.cast_zero]
        have : (0 : ℝ) ≤ (1 - c + η) ^ b := pow_nonneg hc0 b
        positivity
    rw [e]; push_cast
    calc ∑ p : (Fin L → Fin Q → Ω), ((univ.filter (fun f : (Fin b → Ω) =>
          (∀ j, ¬ Fail J K κ η p j) ∧ BadF J K κ η p (M p) f)).card : ℝ)
        ≤ ∑ _p : (Fin L → Fin Q → Ω), ((L * Q + q) * (1 - c + η) ^ b + b * η) * Fintype.card (Fin b → Ω) :=
          Finset.sum_le_sum fun p _ => hper p
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h' : ((univ.filter (fun x : (Fin L → Fin Q → Ω) × (Fin b → Ω) =>
      ¬ SampleGood J K (M x.1) (pvals x.1) (pvals x.1 ∪ fvals x.2))).card : ℝ) ≤
      A1.card + A2.card := by exact_mod_cast h
  rw [Fintype.card_prod]; push_cast
  nlinarith

end TypedTriangle
