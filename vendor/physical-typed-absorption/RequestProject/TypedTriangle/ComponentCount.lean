/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ActiveCover
public import RequestProject.TypedTriangle.RoutingConstants

@[expose] public section

/-!
# Conteo real de componentes activas por raíz (V17, §1)

Con las definiciones reales `ComponentRows.comp` y `ActiveCover.IsActiveRow`:

* `mem_comp_self`, `isActiveRow_nonempty` — toda fila activa es no vacía;
* `comp_eq_or_disjoint` — dos componentes del enlace de una misma raíz son iguales o
  disjuntas (las componentes son clases de `Reachable`);
* `activeRowsAt_pairwiseDisjoint` — las filas activas de raíz fija tienen conjuntos
  disjuntos dos a dos;
* `sum_card_activeRowsAt_le` — su tamaño total es `≤ card V`;
* `card_activeRowsAt_mul_le` — con la cota inferior `α · card V ≤ |K|`, el número de filas
  activas por raíz por `α · card V` es `≤ card V`;
* `hrows_of_lower` y `hdeg_of_lower` — exactamente `hrows` y `hdeg` de
  `routing_budget_real` con `C = compConst α = max 1 ⌈1/α⌉₊`.

El caso `card V = 0` se trata aparte (no hay filas activas), sin cancelar ceros. No se
enumera ninguna clase de etiquetas ni se supone ninguna cota sobre ellas.
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.ComponentCount

open TypedTriangle.ComponentRows TypedTriangle.ActiveCover TypedTriangle.RoutingConstants

variable {V I : Type*} [Fintype V] (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))

/-- Filas activas de raíz `a` (el conjunto filtrado de `hrows`). -/
def activeRowsAt (a : V) : Finset (Row V) :=
  univ.filter (fun j : Row V => j.1 = a ∧ IsActiveRow G lab F j)

lemma mem_activeRowsAt {a : V} {j : Row V} :
    j ∈ activeRowsAt G lab F a ↔ j.1 = a ∧ IsActiveRow G lab F j := by
  simp [activeRowsAt]

lemma mem_comp_self (v u : V) : u ∈ comp G lab F v u := by
  simp [comp]

lemma mem_comp_iff {v u w : V} : w ∈ comp G lab F v u ↔ (link G lab F v).Reachable u w := by
  simp [comp]

/-- Toda fila activa es no vacía. -/
lemma isActiveRow_nonempty {j : Row V} (hj : IsActiveRow G lab F j) : j.2.Nonempty := by
  obtain ⟨u, -, hu⟩ := hj
  exact ⟨u, hu ▸ mem_comp_self G lab F _ u⟩

/-- Dos componentes del enlace de una misma raíz son iguales o disjuntas. -/
lemma comp_eq_or_disjoint (v u w : V) :
    comp G lab F v u = comp G lab F v w ∨ Disjoint (comp G lab F v u) (comp G lab F v w) := by
  by_cases h : (link G lab F v).Reachable u w
  · left
    ext x
    rw [mem_comp_iff, mem_comp_iff]
    exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩
  · right
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_comp_iff] at hx hx'
    exact h (hx.trans hx'.symm)

/-- Las filas activas de raíz fija tienen conjuntos disjuntos dos a dos. -/
lemma activeRowsAt_pairwiseDisjoint (a : V) :
    ((activeRowsAt G lab F a : Finset (Row V)) : Set (Row V)).PairwiseDisjoint Prod.snd := by
  intro j hj k hk hne
  rw [Finset.mem_coe, mem_activeRowsAt] at hj hk
  obtain ⟨hja, u, -, hu⟩ := hj
  obtain ⟨hka, w, -, hw⟩ := hk
  rw [hja] at hu
  rw [hka] at hw
  rcases comp_eq_or_disjoint G lab F a u w with h | h
  · exact absurd (Prod.ext (hja.trans hka.symm) (hu.symm.trans (h.trans hw))) hne
  · show Disjoint j.2 k.2
    rw [← hu, ← hw]
    exact h

/-- El tamaño total de las componentes activas de una raíz es `≤ card V`. -/
theorem sum_card_activeRowsAt_le (a : V) :
    ∑ j ∈ activeRowsAt G lab F a, j.2.card ≤ Fintype.card V := by
  rw [← Finset.card_biUnion (activeRowsAt_pairwiseDisjoint G lab F a)]
  exact card_le_univ _

/-- Sin vértices no hay filas activas. -/
lemma activeRowsAt_eq_empty_of_card_eq_zero (h0 : Fintype.card V = 0) (a : V) :
    activeRowsAt G lab F a = ∅ :=
  absurd h0 (Fintype.card_pos_iff.2 ⟨a⟩).ne'

/-- Con la cota inferior `α · card V ≤ |K|`: `#filas · (α · card V) ≤ card V`. -/
theorem card_activeRowsAt_mul_le {α : ℝ}
    (hlow : ∀ j : Row V, IsActiveRow G lab F j → α * Fintype.card V ≤ j.2.card) (a : V) :
    ((activeRowsAt G lab F a).card : ℝ) * (α * Fintype.card V) ≤ Fintype.card V := by
  have h1 : ((activeRowsAt G lab F a).card : ℝ) * (α * Fintype.card V) ≤
      ∑ j ∈ activeRowsAt G lab F a, (j.2.card : ℝ) := by
    have := Finset.card_nsmul_le_sum (activeRowsAt G lab F a) (fun j => (j.2.card : ℝ))
      (α * Fintype.card V) (fun j hj => hlow j ((mem_activeRowsAt G lab F).1 hj).2)
    simpa [nsmul_eq_mul, mul_comm] using this
  have h2 : ∑ j ∈ activeRowsAt G lab F a, (j.2.card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast sum_card_activeRowsAt_le G lab F a
  linarith

/-- **`hrows` de `routing_budget_real`** con `C = compConst α`. -/
theorem hrows_of_lower {α : ℝ} (hα : 0 < α)
    (hlow : ∀ j : Row V, IsActiveRow G lab F j → α * Fintype.card V ≤ j.2.card) (a : V) :
    (univ.filter (fun j : Row V => j.1 = a ∧ IsActiveRow G lab F j)).card ≤ compConst α := by
  change (activeRowsAt G lab F a).card ≤ compConst α
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · rw [activeRowsAt_eq_empty_of_card_eq_zero G lab F h0 a, card_empty]
    exact Nat.zero_le _
  · have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hpos
    have hm := card_activeRowsAt_mul_le G lab F hlow a
    have hle : ((activeRowsAt G lab F a).card : ℝ) ≤ 1 / α := by
      rw [le_div_iff₀ hα]
      have : ((activeRowsAt G lab F a).card : ℝ) * α * Fintype.card V ≤ 1 * Fintype.card V := by
        linarith
      exact le_of_mul_le_mul_right this hn
    exact_mod_cast hle.trans (inv_le_compConst α)

/-- **`hdeg` de `routing_budget_real`** con `C = compConst α`. -/
theorem hdeg_of_lower {α : ℝ} (hα : 0 < α)
    (hlow : ∀ j : Row V, IsActiveRow G lab F j → α * Fintype.card V ≤ j.2.card)
    (j : Row V) (hj : IsActiveRow G lab F j) : Fintype.card V ≤ compConst α * j.2.card := by
  have hK := hlow j hj
  have hC := inv_le_compConst α
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have : (Fintype.card V : ℝ) ≤ compConst α * j.2.card := by
    calc (Fintype.card V : ℝ) = (1 / α) * (α * Fintype.card V) := by field_simp
      _ ≤ compConst α * j.2.card :=
        mul_le_mul hC hK (by positivity) (by positivity)
  exact_mod_cast this

/-- Caso sin filas activas: el conteo por raíz es `0` y la cota inferior es vacía. -/
lemma activeRowsAt_eq_empty_of_no_active (hno : ∀ j : Row V, ¬ IsActiveRow G lab F j)
    (a : V) : activeRowsAt G lab F a = ∅ := by
  ext j
  simp only [mem_activeRowsAt, Finset.notMem_empty, iff_false, not_and]
  exact fun _ => hno j

/-- Sin filas activas, la cota inferior de componentes activas se cumple para todo `α`. -/
lemma lower_of_no_active (hno : ∀ j : Row V, ¬ IsActiveRow G lab F j) (α : ℝ) :
    ∀ j : Row V, IsActiveRow G lab F j → α * Fintype.card V ≤ j.2.card :=
  fun j hj => absurd hj (hno j)

end TypedTriangle.ComponentCount
