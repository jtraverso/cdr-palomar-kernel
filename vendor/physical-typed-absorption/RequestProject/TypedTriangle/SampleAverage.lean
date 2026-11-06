/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SampleRoots

@[expose] public section

/-!
# G1-Z, §6 de la guía V6 — Conteos sobre la muestra firmada común

Todas las cuentas se hacen sobre el MISMO espacio muestral `Y = XS V × XS Bool`:

* `card_filter_equiv`: transporte de conteos por una biyección (muestra base + signos ↔ muestra
  de la cubierta);
* `card_comps_le`: hay a lo sumo `1/α` componentes activas por enlace (grado mínimo `≥ αn`);
* `sum_highDeg_le_gen`: versión de `sum_highDeg_le` para un espacio muestral arbitrario con una
  cota de evitación;
* `card_avoid_le`: la muestra base evita un conjunto de tamaño `≥ αn` en a lo sumo una fracción
  `(1−α)^Q` de los casos;
* monotonía de H3/H4 en `α` (para clampar `α`).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence Sampler

/-- Transporte de conteos por una biyección. -/
lemma card_filter_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (P : β → Prop) :
    (univ.filter (fun a => P (e a))).card = (univ.filter P).card := by
  refine Finset.card_bij (fun a _ => e a) ?_ ?_ ?_
  · intro a ha; simpa using ha
  · intro a _ b _ hab; exact e.injective hab
  · intro b hb
    exact ⟨e.symm b, by simpa using hb, by simp⟩

variable {V I : Type*} [Fintype V]

/-! ## Monotonía de H3/H4 -/

lemma commonNbrCond_mono {H : Host V I} {F : Set (Multiset I)} {α α' : ℝ}
    (h : CommonNbrCond H F α) (hle : α' ≤ α) : CommonNbrCond H F α' := by
  intro u v huv k hk
  have := h u v huv k hk
  have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
  nlinarith

lemma hingeCond_mono {H : Host V I} {F : Set (Multiset I)} {α α' : ℝ} {h : ℕ}
    (hH : HingeCond H F α h) (hle : α' ≤ α) : HingeCond H F α' h := by
  intro u v a b hab ha hb
  obtain ⟨i, hi1, hi2, hi⟩ := hH u v a b hab ha hb
  refine ⟨i, hi1, hi2, le_trans ?_ hi⟩
  exact mul_le_mul_of_nonneg_right hle (by positivity)

/-! ## Número de componentes activas -/

lemma compOf_disjoint {G : SimpleGraph V} {a b : V} (h : compOf G a ≠ compOf G b) :
    Disjoint (compOf G a) (compOf G b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  exact h ((compOf_eq_of_mem hxa).symm.trans (compOf_eq_of_mem hxb))

/-- Hay a lo sumo `1/α` componentes activas. -/
lemma card_comps_le {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) (v : V) :
    ((comps H F v).card : ℝ) * (α * Fintype.card V) ≤ Fintype.card V := by
  set G := linkGraph H F v
  have hdisj : ∀ K ∈ comps H F v, ∀ K' ∈ comps H F v, K ≠ K' → Disjoint K K' := by
    intro K hK K' hK' hne
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hK'
    exact compOf_disjoint hne
  have hsum : ∑ K ∈ comps H F v, K.card = ((comps H F v).biUnion id).card := by
    rw [Finset.card_biUnion]; · rfl
    intro K hK K' hK' hne; exact hdisj K hK K' hK' hne
  have hle : ((comps H F v).biUnion id).card ≤ Fintype.card V := Finset.card_le_univ _
  have hbig : ∀ K ∈ comps H F v, α * Fintype.card V ≤ (K.card : ℝ) := by
    intro K hK
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨w, hw⟩ := (Finset.mem_filter.1 ha).2
    have h1 := link_minDeg hH3 hw
    have h2 : ((univ.filter (G.Adj a)).card : ℝ) ≤ (compOf G a).card := by
      exact_mod_cast Finset.card_le_card fun y hy =>
        mem_compOf.2 (SimpleGraph.Adj.reachable (G := G) (Finset.mem_filter.1 hy).2)
    linarith
  calc ((comps H F v).card : ℝ) * (α * Fintype.card V)
      = ∑ _K ∈ comps H F v, α * Fintype.card V := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ K ∈ comps H F v, (K.card : ℝ) := Finset.sum_le_sum hbig
    _ = (((comps H F v).biUnion id).card : ℝ) := by exact_mod_cast hsum
    _ ≤ Fintype.card V := by exact_mod_cast hle

/-! ## Aristas sin tercero sobre un espacio muestral arbitrario -/

/-- **Versión general de `sum_highDeg_le`.** -/
theorem sum_highDeg_le_gen {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) {Y : Type*} [Fintype Y] (Wf : Y → Finset V) {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hav : ∀ A : Finset V, α * Fintype.card V ≤ A.card →
      ((univ.filter (fun y => ∀ t ∈ A, t ∉ Wf y)).card : ℝ) ≤ θ * Fintype.card Y) (D : ℕ) :
    (∑ y : Y, ((univ.filter (fun x => D < degIn (noThird H F (Wf y)) x)).card : ℝ)) * (D + 1) ≤
      2 * Fintype.card (Sym2 V) * (θ * Fintype.card Y) := by
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
    exact_mod_cast h1.trans (sum_degIn_le B)
  have hswap : (∑ y : Y, ((noThird H F (Wf y)).card : ℝ)) =
      ∑ e : Sym2 V, ((univ.filter (fun y : Y => e ∈ noThird H F (Wf y))).card : ℝ) := by
    have h1 : ∀ y : Y, ((noThird H F (Wf y)).card : ℝ) =
        ∑ e : Sym2 V, if e ∈ noThird H F (Wf y) then (1 : ℝ) else 0 := by
      intro y; rw [Finset.sum_boole]; simp [Finset.filter_mem_eq_inter]
    have h2 : ∀ e : Sym2 V, ((univ.filter (fun y : Y => e ∈ noThird H F (Wf y))).card : ℝ) =
        ∑ y : Y, if e ∈ noThird H F (Wf y) then (1 : ℝ) else 0 := by
      intro e; rw [Finset.sum_boole]
    simp only [h1, h2]
    exact Finset.sum_comm
  have hedge : ∀ e : Sym2 V,
      ((univ.filter (fun y : Y => e ∈ noThird H F (Wf y))).card : ℝ) ≤ θ * Fintype.card Y := by
    intro e
    by_cases he : HasTri H F e
    · refine le_trans ?_ (hav (thirdsOf H F e) (card_thirds_ge hH3 he))
      exact_mod_cast Finset.card_le_card fun y hy => by
        obtain ⟨-, -, hno⟩ := Finset.mem_filter.1 (Finset.mem_filter.1 hy).2
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun t ht htW => hno t htW ht⟩
    · have : univ.filter (fun y : Y => e ∈ noThird H F (Wf y)) = ∅ := by
        ext y; simp [noThird, he]
      rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  calc (∑ y : Y, ((univ.filter (fun x => D < degIn (noThird H F (Wf y)) x)).card : ℝ)) * (D + 1)
      = ∑ y : Y, ((univ.filter (fun x => D < degIn (noThird H F (Wf y)) x)).card : ℝ) * (D + 1) :=
        Finset.sum_mul _ _ _
    _ ≤ ∑ y : Y, 2 * ((noThird H F (Wf y)).card : ℝ) := Finset.sum_le_sum fun y _ => hper _
    _ = 2 * ∑ e : Sym2 V, ((univ.filter (fun y : Y => e ∈ noThird H F (Wf y))).card : ℝ) := by
        rw [← Finset.mul_sum, hswap]
    _ ≤ 2 * ∑ _e : Sym2 V, θ * Fintype.card Y := by
        gcongr with e; exact hedge e
    _ = 2 * Fintype.card (Sym2 V) * (θ * Fintype.card Y) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-! ## Evitación por la muestra base -/

/-- La muestra base evita un conjunto `A` (`|A| ≥ αn`) en a lo sumo una fracción `(1−α)^Q`. -/
theorem card_avoid_le {L Q b : ℕ} (hL : 1 ≤ L) {α : ℝ} (A : Finset V)
    (hA : α * Fintype.card V ≤ A.card) :
    ((univ.filter (fun y : XS L Q b V × XS L Q b Bool => ∀ t ∈ A, t ∉ baseW y.1)).card : ℝ) ≤
      (1 - α) ^ Q * Fintype.card (XS L Q b V × XS L Q b Bool) := by
  set T := univ.filter (fun p : Fin L → Fin Q → V => ∀ j i, p j i ∉ A)
  have hT : (T.card : ℝ) ≤ (1 - α) ^ Q * Fintype.card (Fin L → Fin Q → V) := by
    refine card_le_of_update (⟨0, hL⟩ : Fin L) T fun p => ⟨univ.filter
      (fun x : Fin Q → V => ∀ i, x i ∉ A), fun x hx => ?_, ?_⟩
    · have := (Finset.mem_filter.1 hx).2 ⟨0, hL⟩
      simp only [Function.update_self] at this
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩
    · rw [card_tuples_avoid]
      have hle : A.card ≤ Fintype.card V := Finset.card_le_univ _
      have hcast : ((Fintype.card V - A.card : ℕ) : ℝ) ≤ (1 - α) * Fintype.card V := by
        rw [Nat.cast_sub hle]; linarith
      have hpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hcast Q
      rw [Fintype.card_fun, Fintype.card_fin]
      push_cast
      rw [mul_pow] at hpow
      exact hpow
  have hsub : univ.filter (fun y : XS L Q b V × XS L Q b Bool => ∀ t ∈ A, t ∉ baseW y.1) ⊆
      univ.filter (fun y : XS L Q b V × XS L Q b Bool => y.1.1 ∈ T) := by
    intro y hy
    have hy' := (Finset.mem_filter.1 hy).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      fun j i hji => hy' _ hji ?_⟩⟩
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨(j, i), Finset.mem_univ _, rfl⟩)
  have e1 : (univ.filter (fun y : XS L Q b V × XS L Q b Bool => y.1.1 ∈ T)).card =
      (univ.filter (fun x : XS L Q b V => x.1 ∈ T)).card * Fintype.card (XS L Q b Bool) :=
    by convert card_filter_fst (β := XS L Q b Bool) (fun x : XS L Q b V => x.1 ∈ T)
  have e2 : (univ.filter (fun x : XS L Q b V => x.1 ∈ T)).card =
      (univ.filter (fun p : Fin L → Fin Q → V => p ∈ T)).card * Fintype.card (Fin b → V) :=
    by convert card_filter_fst (β := Fin b → V) (fun p : Fin L → Fin Q → V => p ∈ T)
  have e3 : univ.filter (fun p : Fin L → Fin Q → V => p ∈ T) = T := by ext; simp
  have h1 := Finset.card_le_card hsub
  rw [e1, e2, e3] at h1
  have h1' : ((univ.filter (fun y : XS L Q b V × XS L Q b Bool => ∀ t ∈ A, t ∉ baseW y.1)).card
      : ℝ) ≤ T.card * Fintype.card (Fin b → V) * Fintype.card (XS L Q b Bool) := by
    exact_mod_cast h1
  refine h1'.trans ?_
  rw [Fintype.card_prod (XS L Q b V), Fintype.card_prod (Fin L → Fin Q → V)]
  push_cast
  have : (0 : ℝ) ≤ Fintype.card (Fin b → V) * Fintype.card (XS L Q b Bool) := by positivity
  nlinarith

end TypedTriangle
