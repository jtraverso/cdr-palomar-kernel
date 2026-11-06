/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Packing
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# Escala de los monitores triangulares (S15 §2, desigualdades (2.2))

Para un monitor triangular `w` con una cobertura por vértices `a ≥ 0`
(`|w(T)| ≤ ∑_{v ∈ T} a_v`, de coste `τ = ∑_v a_v`):

* `seed_monitor_bound`: para toda semilla exacta no negativa `ψ`,
  `∑_T ψ_T |w(T)| ≤ n τ / 2`;
* `packing_monitor_bound`: para todo packing `C` con grado de aristas `≤ Δ`,
  `∑_{T ∈ C} |w(T)| ≤ τ Δ / 2`.

Ambas se apoyan en las identidades de estrella `seed_star_sum` (`∑_{T ∋ v} ψ_T = d(v)/2`) y
`packing_star_count` (`2 · #{T ∈ C : v ∈ T} = d_{E(C)}(v)`).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-- Vecinos de `v` a través de un conjunto de aristas `J`. -/
def nbrsIn (J : Finset (Sym2 V)) (v : V) : Finset V := (univ.erase v).filter (fun w => s(v, w) ∈ J)

lemma card_nbrsIn_triEdges {T : Finset V} (hT : T.card = 3) (v : V) :
    (nbrsIn (triEdges T) v).card = if v ∈ T then 2 else 0 := by
  by_cases hv : v ∈ T
  · rw [if_pos hv]
    have : nbrsIn (triEdges T) v = T.erase v := by
      ext w; simp [nbrsIn, mem_triEdges, hv, and_comm, eq_comm]
    rw [this, Finset.card_erase_of_mem hv, hT]
  · rw [if_neg hv]
    rw [Finset.card_eq_zero]
    ext w; simp [nbrsIn, mem_triEdges, hv]

/-- `∑_{w ≠ v} f(vw) = ∑_T … ` : intercambio para pesos de triángulos. -/
lemma sum_nbrs_bdry (H : Host V I) (F : Set (Multiset I)) (ψ : Finset V → ℝ) (v : V) :
    ∑ w ∈ univ.erase v, bdry H F ψ s(v, w) = 2 * ∑ T ∈ triAt H F v, ψ T := by
  unfold bdry
  rw [Finset.sum_comm]
  rw [Finset.mul_sum, triAt, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT3 := (isAllowed_of_mem_allowed hT).1
  rw [← Finset.mul_sum]
  have : ∑ w ∈ univ.erase v, indR (triEdges T) s(v, w) =
      ((nbrsIn (triEdges T) v).card : ℝ) := by
    unfold nbrsIn
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : s(v, w) ∈ triEdges T <;> simp [indR, h]
  rw [this, card_nbrsIn_triEdges hT3]
  by_cases hv : v ∈ T <;> simp [hv]; ring

/-- **Identidad de estrella para semillas.** Si `∂ψ = 1` en las aristas de `G`, entonces
`2 ∑_{T ∋ v} ψ_T = d_G(v)`. -/
theorem seed_star_sum {H : Host V I} {F : Set (Multiset I)} {ψ : Finset V → ℝ}
    (hψ : ∀ e ∈ edges H, bdry H F ψ e = 1) (v : V) :
    2 * ∑ T ∈ triAt H F v, ψ T = (nbrsIn (edges H) v).card := by
  rw [← sum_nbrs_bdry]
  unfold nbrsIn
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : s(v, w) ∈ edges H
  · simp [h, hψ _ h]
  · simp [h, bdry_eq_zero_of_not_mem H F ψ h]

/-- **(2.2), primera desigualdad.** `∑_T ψ_T |w(T)| ≤ n τ / 2`. -/
theorem seed_monitor_bound {H : Host V I} {F : Set (Multiset I)} {ψ : Finset V → ℝ}
    (hψ : ∀ e ∈ edges H, bdry H F ψ e = 1) (hψ0 : ∀ T ∈ allowed H F, 0 ≤ ψ T)
    (w : Finset V → ℝ) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v)
    (hw : ∀ T ∈ allowed H F, |w T| ≤ ∑ v ∈ T, a v) :
    ∑ T ∈ allowed H F, ψ T * |w T| ≤ Fintype.card V * (∑ v, a v) / 2 := by
  calc ∑ T ∈ allowed H F, ψ T * |w T|
      ≤ ∑ T ∈ allowed H F, ψ T * ∑ v ∈ T, a v :=
        Finset.sum_le_sum fun T hT => mul_le_mul_of_nonneg_left (hw T hT) (hψ0 T hT)
    _ = ∑ v, a v * ∑ T ∈ triAt H F v, ψ T := by
        simp only [Finset.mul_sum, triAt, Finset.sum_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun T _ => ?_
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ ≤ ∑ v, a v * (Fintype.card V / 2) := by
        refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_ (ha v)
        have h1 := seed_star_sum hψ v
        have h2 : ((nbrsIn (edges H) v).card : ℝ) ≤ Fintype.card V := by
          exact_mod_cast (Finset.card_le_univ _)
        linarith
    _ = Fintype.card V * (∑ v, a v) / 2 := by
        rw [← Finset.sum_mul]; ring

/-- **Identidad de estrella para packings.** `2 · #{T ∈ C : v ∈ T} = d_{E(C)}(v)`. -/
theorem packing_star_count {H : Host V I} {F : Set (Multiset I)} {C : Finset (Finset V)}
    (hC : IsPacking H F C) (v : V) :
    2 * (C.filter (v ∈ ·)).card = (nbrsIn (C.biUnion triEdges) v).card := by
  have hdisj : ∀ T ∈ C, ∀ T' ∈ C, T ≠ T' →
      Disjoint (nbrsIn (triEdges T) v) (nbrsIn (triEdges T') v) := by
    intro T hT T' hT' hne
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [nbrsIn, Finset.mem_filter] at h1 h2
    exact Finset.disjoint_left.mp (hC.2 hT hT' hne) h1.2 h2.2
  have hbu : nbrsIn (C.biUnion triEdges) v = C.biUnion (fun T => nbrsIn (triEdges T) v) := by
    ext w; simp [nbrsIn, Finset.mem_biUnion]; tauto
  rw [hbu, Finset.card_biUnion hdisj]
  rw [Finset.card_eq_sum_ones, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [card_nbrsIn_triEdges (hC.1 T hT).1]
  by_cases hv : v ∈ T <;> simp [hv]

/-- **(2.2), segunda desigualdad.** Para un packing `C` con `d_{E(C)}(v) ≤ Δ` para todo `v`,
`∑_{T ∈ C} |w(T)| ≤ τ Δ / 2`. -/
theorem packing_monitor_bound {H : Host V I} {F : Set (Multiset I)} {C : Finset (Finset V)}
    (hC : IsPacking H F C) (Δ : ℝ)
    (hΔ : ∀ v, ((nbrsIn (C.biUnion triEdges) v).card : ℝ) ≤ Δ)
    (w : Finset V → ℝ) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v)
    (hw : ∀ T ∈ C, |w T| ≤ ∑ v ∈ T, a v) :
    ∑ T ∈ C, |w T| ≤ (∑ v, a v) * Δ / 2 := by
  calc ∑ T ∈ C, |w T| ≤ ∑ T ∈ C, ∑ v ∈ T, a v := Finset.sum_le_sum hw
    _ = ∑ v, a v * (C.filter (v ∈ ·)).card := by
        rw [Finset.sum_comm' (t' := univ) (s' := fun v => C.filter (v ∈ ·))]
        · refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        · intro T v; simp
    _ ≤ ∑ v, a v * (Δ / 2) := by
        refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_ (ha v)
        have h1 := packing_star_count hC v
        have h2 := hΔ v
        have : (2 : ℝ) * (C.filter (v ∈ ·)).card = (nbrsIn (C.biUnion triEdges) v).card := by
          exact_mod_cast h1
        linarith
    _ = (∑ v, a v) * Δ / 2 := by rw [← Finset.sum_mul]; ring

end TypedTriangle
