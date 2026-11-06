/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Seed
public import RequestProject.Pseudorandom.Theorem12

@[expose] public section

/-!
# Adaptador de Ehard–Glock–Joos [R1] a packings de triángulos permitidos (entrada de P07)

Se especializa `Pseudorandom.theorem_1_2` (Teorema 1.2 de Ehard–Glock–Joos, demostrado por
completo en `RequestProject/Pseudorandom/`) al hipergrafo 3-uniforme cuyo conjunto de
vértices son las aristas del host y cuyas hiperaristas son los conjuntos `E(T)` de los
triángulos permitidos. Un matching de ese hipergrafo es exactamente un packing de
triángulos permitidos.

* `triEdges_injOn`: `E(T)` determina `T` para conjuntos de tres vértices;
* `triHyper_codegree_le_one`: dos aristas distintas están en a lo sumo un triángulo;
* `typed_packing_EGJ`: packing con pesos aproximados (forma general de [R1] para el host);
* `typed_packing_EGJ_seed`: forma con `Δ = C n`, usando sólo (H1) para el grado.

El muestreo ponderado por la semilla y el padding de monitores de S14 (que dan el residuo
de grado `o(n)` de (L16)) NO están formalizados aquí.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

omit [Fintype V] in
lemma mem_of_mem_triEdges_card {T : Finset V} (hT : T.card = 3) {x : V} :
    x ∈ T ↔ ∃ y, s(x, y) ∈ triEdges T := by
  constructor
  · intro hx
    have : 1 < T.card := by omega
    obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne this x
    exact ⟨y, mem_triEdges.2 ⟨hx, hy, hyx.symm⟩⟩
  · rintro ⟨y, hy⟩
    exact (mem_triEdges.1 hy).1

omit [Fintype V] in
/-- `E(T)` determina `T` entre los conjuntos de tres vértices. -/
lemma triEdges_inj {T T' : Finset V} (hT : T.card = 3) (hT' : T'.card = 3)
    (h : triEdges T = triEdges T') : T = T' := by
  ext x
  rw [mem_of_mem_triEdges_card hT, mem_of_mem_triEdges_card hT', h]

omit [Fintype V] in
/-- Dos aristas distintas de un mismo par de triángulos de tres vértices fuerzan que los
triángulos coincidan. -/
lemma eq_of_two_edges {T T' : Finset V} (hT : T.card = 3) (hT' : T'.card = 3)
    {e f : Sym2 V} (hef : e ≠ f) (heT : e ∈ triEdges T) (hfT : f ∈ triEdges T)
    (heT' : e ∈ triEdges T') (hfT' : f ∈ triEdges T') : T = T' := by
  induction e using Sym2.ind with
  | _ a b =>
  induction f using Sym2.ind with
  | _ c d =>
  rw [mem_triEdges] at heT hfT heT' hfT'
  have key : ∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x ∈ T ∧ y ∈ T ∧ z ∈ T ∧
      x ∈ T' ∧ y ∈ T' ∧ z ∈ T' := by
    by_cases hc : c = a ∨ c = b
    · by_cases hd : d = a ∨ d = b
      · exfalso; apply hef
        rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
        · exact absurd rfl hfT.2.2
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hfT.2.2
      · push_neg at hd
        exact ⟨a, b, d, heT.2.2, hd.1.symm, hd.2.symm, heT.1, heT.2.1, hfT.2.1,
          heT'.1, heT'.2.1, hfT'.2.1⟩
    · push_neg at hc
      exact ⟨a, b, c, heT.2.2, hc.1.symm, hc.2.symm, heT.1, heT.2.1, hfT.1,
        heT'.1, heT'.2.1, hfT'.1⟩
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz, hx', hy', hz'⟩ := key
  have hsub : ({x, y, z} : Finset V) ⊆ T := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hsub' : ({x, y, z} : Finset V) ⊆ T' := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hc3 : ({x, y, z} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_pair hyz]
  have h1 := Finset.eq_of_subset_of_card_le hsub (by rw [hT, hc3])
  have h2 := Finset.eq_of_subset_of_card_le hsub' (by rw [hT', hc3])
  rw [← h1, ← h2]

/-- El hipergrafo de triángulos permitidos sobre las aristas del host. -/
def triHyper (H : Host V I) (F : Set (Multiset I)) : Finset (Finset (Sym2 V)) :=
  (allowed H F).image triEdges

lemma isAllowed_of_mem_allowed {H : Host V I} {F : Set (Multiset I)} {T : Finset V}
    (hT : T ∈ allowed H F) : IsAllowed H F T := by
  simpa [allowed] using hT

lemma triEdges_injOn (H : Host V I) (F : Set (Multiset I)) :
    Set.InjOn triEdges (allowed H F : Set (Finset V)) := by
  intro T hT T' hT' h
  exact triEdges_inj (isAllowed_of_mem_allowed hT).1 (isAllowed_of_mem_allowed hT').1 h

omit [Fintype V] in
lemma card_triEdges_three {T : Finset V} (hT : T.card = 3) : (triEdges T).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT
  have : triEdges ({a, b, c} : Finset V) = {s(a, b), s(a, c), s(b, c)} := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_triEdges]
      simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
      constructor
      · rintro ⟨hx, hy, hxy⟩
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> tauto
      · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [Ne.symm]
  rw [this, Finset.card_insert_of_notMem, Finset.card_pair]
  · intro h; rw [Sym2.eq_iff] at h; tauto
  · simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]; tauto

lemma triHyper_uniform (H : Host V I) (F : Set (Multiset I)) :
    Pseudorandom.IsUniform (triHyper H F) 3 := by
  intro X hX
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hX
  exact card_triEdges_three (isAllowed_of_mem_allowed hT).1

lemma triHyper_degree (H : Host V I) (F : Set (Multiset I)) (e : Sym2 V) :
    Pseudorandom.degree (triHyper H F) e = (triOn H F e).card := by
  unfold Pseudorandom.degree triHyper triOn
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  exact (triEdges_injOn H F).mono (by intro T hT; exact (Finset.mem_filter.mp hT).1)

lemma triHyper_codegree_le_one (H : Host V I) (F : Set (Multiset I)) {e f : Sym2 V}
    (hef : e ≠ f) : Pseudorandom.codegree (triHyper H F) e f ≤ 1 := by
  unfold Pseudorandom.codegree
  rw [Finset.card_le_one]
  intro X hX Y hY
  simp only [Finset.mem_filter, triHyper, Finset.mem_image] at hX hY
  obtain ⟨⟨T, hT, rfl⟩, he, hf⟩ := hX
  obtain ⟨⟨T', hT', rfl⟩, he', hf'⟩ := hY
  rw [eq_of_two_edges (isAllowed_of_mem_allowed hT).1 (isAllowed_of_mem_allowed hT').1
    hef he hf he' hf']

lemma card_triHyper_le (H : Host V I) (F : Set (Multiset I)) :
    (triHyper H F).card ≤ (allowed H F).card := Finset.card_image_le

lemma card_allowed_le (H : Host V I) (F : Set (Multiset I)) :
    (allowed H F).card ≤ Fintype.card V ^ 3 := by
  calc (allowed H F).card ≤ ((Finset.univ : Finset V).powersetCard 3).card := by
        apply Finset.card_le_card
        intro T hT
        exact Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, (isAllowed_of_mem_allowed hT).1⟩
    _ = (Fintype.card V).choose 3 := by rw [Finset.card_powersetCard, Finset.card_univ]
    _ ≤ Fintype.card V ^ 3 := Nat.choose_le_pow _ _

/-- Un packing: triángulos permitidos disjuntos en aristas. -/
def IsPacking (H : Host V I) (F : Set (Multiset I)) (P : Finset (Finset V)) : Prop :=
  (∀ T ∈ P, IsAllowed H F T) ∧ (P : Set (Finset V)).PairwiseDisjoint triEdges

omit [Fintype V] in
/-- Un packing es una descomposición del conjunto de aristas que cubre. -/
lemma IsPacking.isDecomposition {H : Host V I} {F : Set (Multiset I)} {P : Finset (Finset V)}
    (hP : IsPacking H F P) : IsDecomposition H F (P.biUnion triEdges) P :=
  ⟨hP.1, hP.2, rfl⟩

/-- **Adaptador de [R1] a packings tipados.** Para `δ ∈ (0,1)` y `ε = δ/450` existe `Δ₀` tal
que, para `Δ ≥ Δ₀` y todo host en el que cada arista está en a lo sumo `Δ` triángulos
permitidos, con a lo sumo `exp(Δ^{ε²})` triángulos y una familia de a lo sumo `exp(Δ^{ε²})`
pesos no negativos, existe un packing `P` con
`|w(P) − w(𝒯)/Δ| ≤ Δ^{-ε} w(𝒯)/Δ` para cada peso suficientemente extendido. -/
theorem typed_packing_EGJ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ →
    ∀ (V : Type) [Fintype V] (H : Host V I) (F : Set (Multiset I)),
      (∀ e, ((triOn H F e).card : ℝ) ≤ Δ) →
      ((allowed H F).card : ℝ) ≤ Real.exp (Δ ^ ((δ / (50 * 3 ^ 2)) ^ 2)) →
      ∀ (ι : Type) [Fintype ι] (W : ι → Finset V → ℝ),
      (∀ k, ∀ T ∈ allowed H F, 0 ≤ W k T) →
      (Fintype.card ι : ℝ) ≤ Real.exp (Δ ^ ((δ / (50 * 3 ^ 2)) ^ 2)) →
      ∃ P ⊆ allowed H F, IsPacking H F P ∧
        ∀ k, (∀ T ∈ allowed H F, W k T * Δ ^ (1 + δ) ≤ ∑ T ∈ allowed H F, W k T) →
          |∑ T ∈ P, W k T - (∑ T ∈ allowed H F, W k T) / Δ| ≤
            Δ ^ (-(δ / (50 * 3 ^ 2))) * ((∑ T ∈ allowed H F, W k T) / Δ) := by
  obtain ⟨Δ₀, hΔ₀⟩ := Pseudorandom.theorem_1_2 δ hδ0 hδ1 3 (by norm_num)
  refine ⟨max Δ₀ 1, fun Δ hΔ V _ H F hdeg hcard ι _ W hW hι => ?_⟩
  have hΔ1 : (1 : ℝ) ≤ Δ := le_trans (le_max_right _ _) hΔ
  -- pesos sobre hiperaristas
  let W' : ι → Finset (Sym2 V) → ℝ := fun k X =>
    ∑ T ∈ (allowed H F).filter (fun T => triEdges T = X), W k T
  have hW'T : ∀ k, ∀ T ∈ allowed H F, W' k (triEdges T) = W k T := by
    intro k T hT
    simp only [W']
    rw [Finset.sum_eq_single T]
    · intro T' hT' hne
      exact absurd ((triEdges_injOn H F) (Finset.mem_filter.mp hT').1 hT
        (Finset.mem_filter.mp hT').2) hne
    · intro h; exact absurd (Finset.mem_filter.mpr ⟨hT, rfl⟩ :
        T ∈ (allowed H F).filter (fun T' => triEdges T' = triEdges T)) h
  have hweight : ∀ k (S : Finset (Finset V)), S ⊆ allowed H F →
      Pseudorandom.weight (W' k) (S.image triEdges) = ∑ T ∈ S, W k T := by
    intro k S hS
    unfold Pseudorandom.weight
    rw [Finset.sum_image]
    · exact Finset.sum_congr rfl fun T hT => hW'T k T (hS hT)
    · exact (triEdges_injOn H F).mono (fun T hT => hS hT)
  have hcod : ∀ e f : Sym2 V, e ≠ f →
      (Pseudorandom.codegree (triHyper H F) e f : ℝ) ≤ Δ ^ (1 - δ) := by
    intro e f hef
    have h1 : (Pseudorandom.codegree (triHyper H F) e f : ℝ) ≤ 1 := by
      exact_mod_cast triHyper_codegree_le_one H F hef
    exact h1.trans (Real.one_le_rpow hΔ1 (by linarith))
  obtain ⟨M, hMsub, hMmatch, hMw⟩ := hΔ₀ Δ (le_trans (le_max_left _ _) hΔ) (Sym2 V)
    (triHyper H F) (triHyper_uniform H F)
    (fun e => by rw [triHyper_degree]; exact hdeg e) hcod
    (le_trans (show ((triHyper H F).card : ℝ) ≤ (allowed H F).card by
      exact_mod_cast card_triHyper_le H F) (by norm_num at hcard ⊢; exact hcard))
    ι W' (fun k X hX => by
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hX
      rw [hW'T k T hT]; exact hW k T hT)
    (by push_cast at hι ⊢; exact hι)
  -- el packing
  let P := (allowed H F).filter (fun T => triEdges T ∈ M)
  have hPsub : P ⊆ allowed H F := Finset.filter_subset _ _
  have hPM : P.image triEdges = M := by
    ext X
    simp only [P, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨T, ⟨-, hTM⟩, rfl⟩; exact hTM
    · intro hX
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp (hMsub hX)
      exact ⟨T, ⟨hT, hX⟩, rfl⟩
  have hfull : (allowed H F).image triEdges = triHyper H F := rfl
  refine ⟨P, hPsub, ⟨fun T hT => isAllowed_of_mem_allowed (hPsub hT), ?_⟩, fun k hk => ?_⟩
  · intro T hT T' hT' hne
    have hT1 := Finset.mem_filter.mp hT
    have hT1' := Finset.mem_filter.mp hT'
    refine hMmatch _ hT1.2 _ hT1'.2 ?_
    intro h; exact hne ((triEdges_injOn H F) hT1.1 hT1'.1 h)
  · have hk' : ∀ X ∈ triHyper H F, W' k X * Δ ^ (1 + δ) ≤
        Pseudorandom.weight (W' k) (triHyper H F) := by
      intro X hX
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hX
      rw [hW'T k T hT, ← hfull, hweight k _ (subset_refl _)]
      exact hk T hT
    have := hMw k hk'
    rw [← hPM, hweight k P hPsub, ← hfull, hweight k _ (subset_refl _)] at this
    exact this

lemma eventually_cube_le_exp (a C : ℝ) (ha : 0 < a) (hC : 1 ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop, x ^ 3 ≤ Real.exp ((C * x) ^ a) := by
  have h := (isLittleO_log_rpow_atTop ha).bound (show (0:ℝ) < 1/3 by norm_num)
  filter_upwards [h, Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
  have h2 : x ^ a ≤ (C * x) ^ a := Real.rpow_le_rpow hx0.le (by nlinarith) ha.le
  rw [← Real.exp_log (pow_pos hx0 3), Real.exp_le_exp, Real.log_pow]
  push_cast
  linarith

/-- **[R1] con `Δ = C n` bajo (H1).** Para `δ ∈ (0,1)` y `C ≥ 1` existe `n₁` tal que todo
host de orden `n ≥ n₁` con una semilla exacta difusa de constante `C` admite, para cada
familia de a lo sumo `exp((Cn)^{ε²})` pesos no negativos, un packing `P` con
`|w(P) − w(𝒯)/(Cn)| ≤ (Cn)^{-ε} w(𝒯)/(Cn)` para los pesos extendidos. -/
theorem typed_packing_EGJ_seed (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (C : ℝ) (hC : 1 ≤ C) :
    ∃ n₁ : ℕ, ∀ (V : Type) [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), n₁ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      ∀ (ι : Type) [Fintype ι] (W : ι → Finset V → ℝ),
      (∀ k, ∀ T ∈ allowed H F, 0 ≤ W k T) →
      (Fintype.card ι : ℝ) ≤
        Real.exp ((C * Fintype.card V) ^ ((δ / (50 * 3 ^ 2)) ^ 2)) →
      ∃ P ⊆ allowed H F, IsPacking H F P ∧
        ∀ k, (∀ T ∈ allowed H F,
            W k T * (C * Fintype.card V) ^ (1 + δ) ≤ ∑ T ∈ allowed H F, W k T) →
          |∑ T ∈ P, W k T - (∑ T ∈ allowed H F, W k T) / (C * Fintype.card V)| ≤
            (C * Fintype.card V) ^ (-(δ / (50 * 3 ^ 2))) *
              ((∑ T ∈ allowed H F, W k T) / (C * Fintype.card V)) := by
  obtain ⟨Δ₀, hΔ₀⟩ := typed_packing_EGJ (I := I) δ hδ0 hδ1
  have hC0 : 0 < C := by linarith
  have hev : ∀ᶠ x : ℝ in Filter.atTop, Δ₀ ≤ C * x ∧
      x ^ 3 ≤ Real.exp ((C * x) ^ ((δ / (50 * 3 ^ 2)) ^ 2)) := by
    refine (Filter.eventually_ge_atTop (Δ₀ / C)).and
      (eventually_cube_le_exp _ C (by positivity) hC) |>.mono fun x hx => ⟨?_, hx.2⟩
    have := hx.1
    rw [div_le_iff₀ hC0] at this; linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨⌈N⌉₊, fun V _ H F φ hn hφ ι _ W hW hι => ?_⟩
  have hnN : N ≤ (Fintype.card V : ℝ) := (Nat.le_ceil N).trans (by exact_mod_cast hn)
  obtain ⟨h1, h2⟩ := hN _ hnN
  refine hΔ₀ (C * Fintype.card V) h1 V H F (fun e => ?_) ?_ ι W hW hι
  · by_cases he : e ∈ H.G.edgeSet
    · exact card_triOn_le hφ hC0 he
    · have : triOn H F e = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun T hT heT => he ?_
        have := triEdges_subset_edges (isAllowed_of_mem_allowed hT) heT
        simpa [edges] using this
      rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  · calc ((allowed H F).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 3 := by
          exact_mod_cast card_allowed_le H F
      _ ≤ _ := h2

end TypedTriangle
