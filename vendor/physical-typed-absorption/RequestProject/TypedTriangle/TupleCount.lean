/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.LinkCover

@[expose] public section

/-!
# G1-Z, §4 de la guía V6 — Conteos finitos de extensiones de tuplas

Herramientas de conteo para el muestreo con reemplazo, sin teoría de probabilidad:

* `card_update_le`: si, fijadas las demás coordenadas, a lo sumo una fracción `μ` de los valores
  de la coordenada `j` satisface `E`, entonces a lo sumo una fracción `μ` de todas las tuplas
  satisface `E`. Es la forma finita de «condicionar en las coordenadas previas»: los conjuntos
  buenos pueden depender de las otras coordenadas.
* `card_tuples_hit_le`: `#{f : Fin b → Ω | ∃ i, f i ∈ A} ≤ b (|A|/N) N^b`.
* `card_filter_fst`, `card_filter_prod`: conteos sobre productos.
* `one_sub_pow_le_inv`: `(1−p)^m ≤ 1/(1+mp)` para `p ∈ [0,1]`.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

/-- **Condicionamiento finito en una coordenada** (forma con un conjunto explícito). -/
theorem card_le_of_update {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] (j : ι)
    (T : Finset (ι → β)) {μ : ℝ}
    (h : ∀ p : ι → β, ∃ s : Finset β, (∀ x, Function.update p j x ∈ T → x ∈ s) ∧
      (s.card : ℝ) ≤ μ * Fintype.card β) :
    (T.card : ℝ) ≤ μ * Fintype.card (ι → β) := by
  -- involución `(p, x) ↦ (update p j x, p j)`
  let e : (ι → β) × β ≃ (ι → β) × β :=
    { toFun := fun px => (Function.update px.1 j px.2, px.1 j)
      invFun := fun px => (Function.update px.1 j px.2, px.1 j)
      left_inv := fun px => by simp
      right_inv := fun px => by simp }
  set U := univ.filter (fun px : (ι → β) × β => Function.update px.1 j px.2 ∈ T)
  have h1 : U.card = (T ×ˢ (univ : Finset β)).card := by
    refine Finset.card_bij (fun px _ => e px) ?_ ?_ ?_
    · intro px hpx
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hpx
      simpa [e] using hpx
    · intro a _ b _ hab; exact e.injective hab
    · intro qy hqy
      refine ⟨e.symm qy, ?_, by simp⟩
      simp only [Finset.mem_product, Finset.mem_univ, and_true] at hqy
      simpa [U, e] using hqy
  have h3 : U.card = ∑ p : ι → β, (univ.filter (fun x : β => Function.update p j x ∈ T)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun p _ => (Finset.card_filter _ _).symm
  have key : (T.card : ℝ) * Fintype.card β ≤ μ * Fintype.card (ι → β) * Fintype.card β := by
    have h4 : (T.card : ℝ) * Fintype.card β =
        ∑ p : ι → β, ((univ.filter (fun x : β => Function.update p j x ∈ T)).card : ℝ) := by
      have : T.card * Fintype.card β =
          ∑ p : ι → β, (univ.filter (fun x : β => Function.update p j x ∈ T)).card := by
        rw [← h3, h1, Finset.card_product, Finset.card_univ]
      exact_mod_cast this
    rw [h4]
    calc ∑ p : ι → β, ((univ.filter (fun x : β => Function.update p j x ∈ T)).card : ℝ)
        ≤ ∑ _p : ι → β, μ * Fintype.card β := Finset.sum_le_sum fun p _ => by
          obtain ⟨s, hs, hsc⟩ := h p
          refine le_trans ?_ hsc
          exact_mod_cast Finset.card_le_card fun x hx => hs x (Finset.mem_filter.1 hx).2
      _ = μ * Fintype.card (ι → β) * Fintype.card β := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  by_cases hβ : (Fintype.card β : ℝ) = 0
  · have hβ' : Fintype.card β = 0 := by exact_mod_cast hβ
    have : IsEmpty β := Fintype.card_eq_zero_iff.1 hβ'
    have : IsEmpty (ι → β) := ⟨fun p => IsEmpty.false (p j)⟩
    simp [Finset.eq_empty_of_isEmpty T]
  · have hpos : (0 : ℝ) < Fintype.card β := lt_of_le_of_ne (by positivity) (Ne.symm hβ)
    exact le_of_mul_le_mul_right key hpos

/-- **Condicionamiento finito en una coordenada.** -/
theorem card_update_le {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] (j : ι)
    (E : (ι → β) → Prop) {μ : ℝ}
    (h : ∀ p : ι → β, ((univ.filter (fun x : β => E (Function.update p j x))).card : ℝ) ≤
      μ * Fintype.card β) :
    ((univ.filter E).card : ℝ) ≤ μ * Fintype.card (ι → β) :=
  card_le_of_update j _ fun p => ⟨univ.filter (fun x : β => E (Function.update p j x)),
    fun _ hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hx).2⟩, h p⟩

/-- Tuplas que tocan un conjunto. -/
theorem card_tuples_hit_le {Ω : Type*} [Fintype Ω] (b : ℕ) (A : Finset Ω) :
    ((univ.filter (fun f : Fin b → Ω => ∃ i, f i ∈ A)).card : ℝ) ≤
      b * ((A.card : ℝ) / Fintype.card Ω) * Fintype.card (Fin b → Ω) := by
  have hsub : univ.filter (fun f : Fin b → Ω => ∃ i, f i ∈ A) ⊆
      univ.biUnion (fun i : Fin b => univ.filter (fun f : Fin b → Ω => f i ∈ A)) := by
    intro f hf
    obtain ⟨i, hi⟩ := (Finset.mem_filter.1 hf).2
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∀ i : Fin b, ((univ.filter (fun f : Fin b → Ω => f i ∈ A)).card : ℝ) ≤
      ((A.card : ℝ) / Fintype.card Ω) * Fintype.card (Fin b → Ω) := by
    intro i
    refine le_of_eq_of_le (by congr 2; ext; simp)
      (card_update_le (μ := (A.card : ℝ) / Fintype.card Ω) i (fun f : Fin b → Ω => f i ∈ A)
        fun p => ?_)
    have hs : univ.filter (fun x : Ω => (fun f : Fin b → Ω => f i ∈ A)
        (Function.update p i x)) ⊆ A := fun x hx => by
      have := (Finset.mem_filter.1 hx).2
      simpa using this
    have hc : ((univ.filter (fun x : Ω => (fun f : Fin b → Ω => f i ∈ A)
        (Function.update p i x))).card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hs
    have hA : (A.card : ℝ) = A.card / Fintype.card Ω * Fintype.card Ω := by
      by_cases hN : (Fintype.card Ω : ℝ) = 0
      · have : Fintype.card Ω = 0 := by exact_mod_cast hN
        have : IsEmpty Ω := Fintype.card_eq_zero_iff.1 this
        simp [Finset.eq_empty_of_isEmpty A]
      · rw [div_mul_cancel₀ _ hN]
    convert hc.trans (le_of_eq hA) using 3
    ext x; simp
  calc ((univ.filter (fun f : Fin b → Ω => ∃ i, f i ∈ A)).card : ℝ)
      ≤ ∑ i : Fin b, ((univ.filter (fun f : Fin b → Ω => f i ∈ A)).card : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ _i : Fin b, ((A.card : ℝ) / Fintype.card Ω) * Fintype.card (Fin b → Ω) :=
        Finset.sum_le_sum fun i _ => h2 i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Conteo de un suceso que sólo depende de la primera coordenada. -/
lemma card_filter_fst {α β : Type*} [Fintype α] [Fintype β] (P : α → Prop) :
    (univ.filter (fun x : α × β => P x.1)).card = (univ.filter P).card * Fintype.card β := by
  rw [show univ.filter (fun x : α × β => P x.1) = (univ.filter P) ×ˢ univ by ext; simp,
    Finset.card_product, Finset.card_univ]

/-- Conteo sobre un producto, fibra a fibra. -/
lemma card_filter_prod {α β : Type*} [Fintype α] [Fintype β] (R : α → β → Prop) :
    (univ.filter (fun x : α × β => R x.1 x.2)).card =
      ∑ a : α, (univ.filter (fun y : β => R a y)).card := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => (Finset.card_filter _ _).symm

/-- `(1 − p)^m ≤ 1/(1 + mp)` para `p ∈ [0,1]`. -/
lemma one_sub_pow_le_inv {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    (1 - p) ^ m ≤ 1 / (1 + m * p) := by
  rw [le_div_iff₀ (by positivity)]
  induction m with
  | zero => simp
  | succ m ih =>
    have h0 : 0 ≤ 1 - p := by linarith
    have h1 : 0 ≤ (1 - p) ^ m := pow_nonneg h0 m
    push_cast
    have e : (1 - p) ^ (m + 1) * (1 + (m + 1) * p) =
        (1 - p) ^ m * (1 + m * p) - (1 - p) ^ m * ((m + 1) * p ^ 2) := by ring
    rw [e]
    have : 0 ≤ (1 - p) ^ m * ((m + 1) * p ^ 2) := by positivity
    linarith

end TypedTriangle
