/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ImageTransfer

@[expose] public section

/-!
# G1-Z, §5 de la guía V5 — Conteo muestral para el grafo `B` (aristas sin tercero en `W`)

Espacio muestral finito: tuplas `w : Fin s → V` (muestras uniformes con reemplazo); el
conjunto muestral es `W(w) = image w`. Las probabilidades se expresan contando tuplas.

* `card_tuples_avoid`: `#{w | ∀ i, w i ∉ A} = (n − |A|)^s`.
* `card_thirds_ge` (de H3): toda arista con triángulo tiene `≥ αn` terceros permitidos.
* `sum_card_noThird_le`: `Σ_w |B(w)| ≤ |Sym2 V| ((1−α)n)^s`, donde `B(w)` son las aristas con
  triángulo sin tercero en `W(w)` (cada arista falla con «probabilidad» `≤ (1−α)^s`).
* `sum_highDeg_le`: `Σ_w #{x : d_{B(w)}(x) > D}·(D+1) ≤ 2|Sym2 V|((1−α)n)^s` — la esperanza
  del número de raíces de grado `> D` en `B`, que se guardan en `Z`.
* `badEdges_subset_noThird`: el grafo `B` de `SampleOut` está contenido en `B(W)`.

Esta es la parte del muestreo relativa a `B`; la conservación de componentes y del carácter
bipartito de los enlaces (raíces buenas) sigue abierta.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence

variable {V I : Type*} [Fintype V] {H : Host V I} {F : Set (Multiset I)}

/-- Terceros permitidos de una arista. -/
def thirdsOf (H : Host V I) (F : Set (Multiset I)) (e : Sym2 V) : Finset V :=
  univ.filter (fun t => ∃ u v, e = s(u, v) ∧ IsAllowed H F {u, v, t})

/-- Aristas con triángulo y sin tercero en `W`. -/
def noThird (H : Host V I) (F : Set (Multiset I)) (W : Finset V) : Finset (Sym2 V) :=
  univ.filter (fun e => HasTri H F e ∧ ∀ t ∈ W, t ∉ thirdsOf H F e)

lemma badEdges_subset_noThird (W Z : Finset V) : badEdges H F W Z ⊆ noThird H F W := by
  intro e he
  obtain ⟨-, hT, -, hno⟩ := Finset.mem_filter.1 he
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hT, fun t ht htT => hno ?_⟩
  obtain ⟨u, v, rfl, hTa⟩ := (Finset.mem_filter.1 htT).2
  exact ⟨u, v, t, rfl, ht, hTa⟩

/-- De H3: toda arista con triángulo tiene al menos `αn` terceros. -/
lemma card_thirds_ge {α : ℝ} (hH3 : CommonNbrCond H F α) {e : Sym2 V} (he : HasTri H F e) :
    α * Fintype.card V ≤ (thirdsOf H F e).card := by
  obtain ⟨u, v, t, rfl, hTa⟩ := he.exists_tri
  obtain ⟨huv, hut, hvt⟩ := distinct_of_card_three hTa.1
  have hlab : ({H.lab u, H.lab v, H.lab t} : Multiset I) ∈ F := by
    have := hTa.2.2
    rwa [Finset.insert_val_of_notMem (by simp [huv, hut]),
      Finset.insert_val_of_notMem (by simp [hvt])] at this
  refine (hH3 u v huv (H.lab t) hlab).trans ?_
  have hsub : commonNbrs H (H.lab t) u v ⊆ thirdsOf H F s(u, v) := fun t' ht' =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, u, v, rfl, allowed_of_commonNbr hTa ht'⟩
  exact_mod_cast Finset.card_le_card hsub

/-- Tuplas que evitan un conjunto. -/
lemma card_tuples_avoid (s : ℕ) (A : Finset V) :
    (univ.filter (fun w : Fin s → V => ∀ i, w i ∉ A)).card = (Fintype.card V - A.card) ^ s := by
  have : univ.filter (fun w : Fin s → V => ∀ i, w i ∉ A) = Fintype.piFinset (fun _ => Aᶜ) := by
    ext w; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset, Finset.prod_const, Finset.card_compl, Finset.card_univ,
    Fintype.card_fin]

/-- Una arista con triángulo cae en `B(w)` para a lo sumo `((1−α)n)^s` tuplas. -/
lemma card_tuples_noThird_le {α : ℝ} (hH3 : CommonNbrCond H F α) (s : ℕ)
    {e : Sym2 V} (he : HasTri H F e) :
    ((univ.filter (fun w : Fin s → V => e ∈ noThird H F (univ.image w))).card : ℝ) ≤
      ((1 - α) * Fintype.card V) ^ s := by
  have hsub : univ.filter (fun w : Fin s → V => e ∈ noThird H F (univ.image w)) ⊆
      univ.filter (fun w : Fin s → V => ∀ i, w i ∉ thirdsOf H F e) := by
    intro w hw
    obtain ⟨-, -, hno⟩ := Finset.mem_filter.1 (Finset.mem_filter.1 hw).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i => hno (w i) (by simp)⟩
  have h1 := Finset.card_le_card hsub
  rw [card_tuples_avoid] at h1
  have hle : (thirdsOf H F e).card ≤ Fintype.card V := Finset.card_le_univ _
  have h2 : ((Fintype.card V - (thirdsOf H F e).card : ℕ) : ℝ) ≤ (1 - α) * Fintype.card V := by
    rw [Nat.cast_sub hle]
    have := card_thirds_ge hH3 he
    linarith
  calc ((univ.filter (fun w : Fin s → V => e ∈ noThird H F (univ.image w))).card : ℝ)
      ≤ ((Fintype.card V - (thirdsOf H F e).card : ℕ) : ℝ) ^ s := by exact_mod_cast h1
    _ ≤ ((1 - α) * Fintype.card V) ^ s := pow_le_pow_left₀ (by positivity) h2 s

/-- **Esperanza del tamaño de `B`.** -/
theorem sum_card_noThird_le {α : ℝ} (hα : α ≤ 1) (hH3 : CommonNbrCond H F α) (s : ℕ) :
    (∑ w : Fin s → V, ((noThird H F (univ.image w)).card : ℝ)) ≤
      Fintype.card (Sym2 V) * ((1 - α) * Fintype.card V) ^ s := by
  have hswap : (∑ w : Fin s → V, ((noThird H F (univ.image w)).card : ℝ)) =
      ∑ e : Sym2 V, ((univ.filter (fun w : Fin s → V =>
        e ∈ noThird H F (univ.image w))).card : ℝ) := by
    have h1 : ∀ w : Fin s → V, ((noThird H F (univ.image w)).card : ℝ) =
        ∑ e : Sym2 V, if e ∈ noThird H F (univ.image w) then (1 : ℝ) else 0 := by
      intro w; rw [Finset.sum_boole]; simp [Finset.filter_mem_eq_inter]
    have h2 : ∀ e : Sym2 V, ((univ.filter (fun w : Fin s → V =>
        e ∈ noThird H F (univ.image w))).card : ℝ) =
        ∑ w : Fin s → V, if e ∈ noThird H F (univ.image w) then (1 : ℝ) else 0 := by
      intro e; rw [Finset.sum_boole]
    simp only [h1, h2]
    exact Finset.sum_comm
  rw [hswap]
  calc ∑ e : Sym2 V, ((univ.filter (fun w : Fin s → V =>
        e ∈ noThird H F (univ.image w))).card : ℝ)
      ≤ ∑ _e : Sym2 V, ((1 - α) * Fintype.card V) ^ s := by
        refine Finset.sum_le_sum fun e _ => ?_
        by_cases he : HasTri H F e
        · exact card_tuples_noThird_le hH3 s he
        · have : univ.filter (fun w : Fin s → V => e ∈ noThird H F (univ.image w)) = ∅ := by
            ext w; simp [noThird, he]
          rw [this]; simp only [Finset.card_empty, Nat.cast_zero]
          have : (0 : ℝ) ≤ 1 - α := by linarith
          positivity
    _ = Fintype.card (Sym2 V) * ((1 - α) * Fintype.card V) ^ s := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `Σ_x d_B(x) ≤ 2|B|`. -/
lemma sum_degIn_le (B : Finset (Sym2 V)) : ∑ x, degIn B x ≤ 2 * B.card := by
  unfold degIn
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  have : univ.filter (fun x => x ∈ e) = e.toFinset := by ext x; simp
  rw [this, Sym2.card_toFinset]
  split_ifs <;> omega

/-- **Esperanza del número de raíces de grado alto en `B`.** -/
theorem sum_highDeg_le {α : ℝ} (hα : α ≤ 1) (hH3 : CommonNbrCond H F α) (s D : ℕ) :
    (∑ w : Fin s → V, ((univ.filter (fun x =>
        D < degIn (noThird H F (univ.image w)) x)).card : ℝ)) * (D + 1) ≤
      2 * Fintype.card (Sym2 V) * ((1 - α) * Fintype.card V) ^ s := by
  have hper : ∀ B : Finset (Sym2 V),
      ((univ.filter (fun x => D < degIn B x)).card : ℝ) * (D + 1) ≤ 2 * B.card := by
    intro B
    have h1 : (univ.filter (fun x => D < degIn B x)).card * (D + 1) ≤ ∑ x, degIn B x := by
      calc (univ.filter (fun x => D < degIn B x)).card * (D + 1)
          = ∑ _x ∈ univ.filter (fun x => D < degIn B x), (D + 1) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ x ∈ univ.filter (fun x => D < degIn B x), degIn B x :=
            Finset.sum_le_sum fun x hx => (Finset.mem_filter.1 hx).2
        _ ≤ ∑ x, degIn B x := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have h2 := (h1.trans (sum_degIn_le B))
    exact_mod_cast h2
  calc (∑ w : Fin s → V, ((univ.filter (fun x =>
        D < degIn (noThird H F (univ.image w)) x)).card : ℝ)) * (D + 1)
      = ∑ w : Fin s → V, ((univ.filter (fun x =>
        D < degIn (noThird H F (univ.image w)) x)).card : ℝ) * (D + 1) := Finset.sum_mul _ _ _
    _ ≤ ∑ w : Fin s → V, 2 * ((noThird H F (univ.image w)).card : ℝ) :=
        Finset.sum_le_sum fun w _ => hper _
    _ = 2 * ∑ w : Fin s → V, ((noThird H F (univ.image w)).card : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (Fintype.card (Sym2 V) * ((1 - α) * Fintype.card V) ^ s) := by
        have := sum_card_noThird_le hα hH3 s; linarith
    _ = 2 * Fintype.card (Sym2 V) * ((1 - α) * Fintype.card V) ^ s := by ring

end TypedTriangle
