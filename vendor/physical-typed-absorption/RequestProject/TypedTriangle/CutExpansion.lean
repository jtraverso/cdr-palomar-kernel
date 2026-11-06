/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.LinkReach

@[expose] public section

/-!
# G1-Z, §3 de la guía V6 — Expansión por cortes y borrados permitidos (S03 §§5–6)

Marco abstracto: un grafo `J` sobre un tipo finito `Ω` (`N = |Ω|`), un conjunto `K` cerrado
para la adyacencia, de grado mínimo `≥ cN`, y **conexión robusta**: borrar `≤ ζN` vértices y
un conjunto de aristas de grado `≤ ρN` no desconecta dos supervivientes de `K`.

`expansion_of_robust`: para todo corte `K = S ⊔ T` con `|S| ≥ cN` y `|T| ≥ ηN`, hay al menos
`κηN` vértices de `S` con al menos `κηN` vecinos en `T`, con `κ = min(c/4, ρζ/16)`
independiente de `η` y de `N`.

* Lado pequeño (`|T| ≤ cN/2`): el grado mínimo da `e(S,T) ≥ |T|cN/2`.
* Ambos lados grandes: si `e(S,T) < (ρζ/8)N²`, se marcan los vértices de carga cruzada
  `> ρN` (menos de `ζN/4`), se borran éstos y las aristas cruzadas restantes (grado `≤ ρN`), y
  la conexión robusta da un recorrido de `S` a `T` sin arista cruzada: contradicción.

No se usa el diámetro ni teoría espectral.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {Ω : Type*} [Fintype Ω]

/-- `K` es cerrado para la adyacencia de `J`. -/
def NbrClosed (J : SimpleGraph Ω) (K : Finset Ω) : Prop := ∀ x ∈ K, ∀ y, J.Adj x y → y ∈ K

/-- Grado mínimo `≥ cN` en `K`. -/
def MinDegOn (J : SimpleGraph Ω) (K : Finset Ω) (c : ℝ) : Prop :=
  ∀ x ∈ K, c * Fintype.card Ω ≤ (univ.filter (J.Adj x)).card

/-- Conexión robusta de `K` en `J` frente a borrados de `≤ ζN` vértices y aristas de grado
`≤ ρN`. -/
def RobustConn (J : SimpleGraph Ω) (K : Finset Ω) (ζ ρ : ℝ) : Prop :=
  ∀ (Z : Finset Ω) (B : Finset (Sym2 Ω)), (Z.card : ℝ) ≤ ζ * Fintype.card Ω →
    (∀ x, (degIn B x : ℝ) ≤ ρ * Fintype.card Ω) →
    ∀ a ∈ K, ∀ b ∈ K, a ∉ Z → b ∉ Z → (delG J Z B).Reachable a b

/-- Vecinos de `x` en `A`. -/
abbrev nbIn (J : SimpleGraph Ω) (A : Finset Ω) (x : Ω) : Finset Ω := A.filter (J.Adj x)

omit [Fintype Ω] in
lemma cut_count_symm (J : SimpleGraph Ω) (S T : Finset Ω) :
    ∑ x ∈ S, (nbIn J T x).card = ∑ y ∈ T, (nbIn J S y).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  simp [J.adj_comm]

omit [Fintype Ω] in
lemma card_nbIn_le_card (J : SimpleGraph Ω) (A : Finset Ω) (x : Ω) :
    (nbIn J A x).card ≤ A.card := Finset.card_filter_le _ _

omit [Fintype Ω] in
/-- Partición de una suma en la parte de valores grandes y la de valores pequeños. -/
lemma sum_le_split (S : Finset Ω) (f : Ω → ℝ) {θ U : ℝ} (hθ : 0 ≤ θ) (hU : ∀ x ∈ S, f x ≤ U) :
    ∑ x ∈ S, f x ≤ (S.filter (fun x => θ ≤ f x)).card * U + S.card * θ := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun x => θ ≤ f x)]
  have h1 : ∑ x ∈ S.filter (fun x => θ ≤ f x), f x ≤
      (S.filter (fun x => θ ≤ f x)).card * U := by
    have := Finset.sum_le_card_nsmul (S.filter (fun x => θ ≤ f x)) f U fun x hx => hU x (Finset.mem_filter.1 hx).1
    rwa [nsmul_eq_mul] at this
  have h2 : ∑ x ∈ S.filter (fun x => ¬ θ ≤ f x), f x ≤
      (S.filter (fun x => ¬ θ ≤ f x)).card * θ := by
    have := Finset.sum_le_card_nsmul (S.filter (fun x => ¬ θ ≤ f x)) f θ fun x hx =>
      le_of_lt (not_le.1 (Finset.mem_filter.1 hx).2)
    rwa [nsmul_eq_mul] at this
  have h3 : ((S.filter (fun x => ¬ θ ≤ f x)).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_filter_le _ _
  nlinarith

/-- Lado pequeño: el grado mínimo da la expansión. -/
lemma expansion_small_side {J : SimpleGraph Ω} {K : Finset Ω} {c : ℝ} (hc : 0 < c)
    (hK : NbrClosed J K) (hdeg : MinDegOn J K c) {S : Finset Ω} {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hTη : η * Fintype.card Ω ≤ (K \ S).card)
    (hTs : ((K \ S).card : ℝ) ≤ c * Fintype.card Ω / 2) :
    c / 4 * η * Fintype.card Ω ≤
      ((S.filter (fun x => c / 4 * η * Fintype.card Ω ≤ (nbIn J (K \ S) x).card)).card : ℝ) := by
  set T := K \ S
  set N : ℝ := (Fintype.card Ω : ℝ)
  have hN0 : 0 ≤ N := by positivity
  -- cada `y ∈ T` tiene `≥ cN − |T|` vecinos en `S`
  have hy : ∀ y ∈ T, c * N - T.card ≤ (nbIn J S y).card := by
    intro y hyT
    have hyK : y ∈ K := (Finset.mem_sdiff.1 hyT).1
    have hsub : univ.filter (J.Adj y) ⊆ nbIn J S y ∪ T := by
      intro z hz
      have hz' := (Finset.mem_filter.1 hz).2
      have hzK := hK y hyK z hz'
      by_cases hzS : z ∈ S
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hzS, hz'⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hzK, hzS⟩)
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 := hdeg y hyK
    have : ((univ.filter (J.Adj y)).card : ℝ) ≤ (nbIn J S y).card + T.card := by exact_mod_cast h1
    linarith
  have he1 : (T.card : ℝ) * (c * N / 2) ≤ ∑ y ∈ T, ((nbIn J S y).card : ℝ) := by
    calc (T.card : ℝ) * (c * N / 2) = ∑ _y ∈ T, (c * N / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ T, ((nbIn J S y).card : ℝ) :=
          Finset.sum_le_sum fun y hyT => by have := hy y hyT; linarith
  have hsym : ∑ y ∈ T, ((nbIn J S y).card : ℝ) = ∑ x ∈ S, ((nbIn J T x).card : ℝ) := by
    exact_mod_cast (cut_count_symm J S T).symm
  set θ : ℝ := c * T.card / 4
  have hθ : 0 ≤ θ := by positivity
  have hsplit := sum_le_split S (fun x => ((nbIn J T x).card : ℝ)) hθ
    (U := T.card) fun x _ => by
      show ((nbIn J T x).card : ℝ) ≤ T.card; exact_mod_cast card_nbIn_le_card J T x
  set M := S.filter (fun x => θ ≤ ((nbIn J T x).card : ℝ))
  have hSN : (S.card : ℝ) ≤ N := by
    show (S.card : ℝ) ≤ (Fintype.card Ω : ℝ); exact_mod_cast Finset.card_le_univ S
  -- `|M| |T| ≥ |T| cN/4`
  have hM : (M.card : ℝ) * T.card ≥ T.card * (c * N / 4) := by
    have : (S.card : ℝ) * θ ≤ N * θ := mul_le_mul_of_nonneg_right hSN hθ
    simp only [θ] at this hsplit
    nlinarith
  by_cases hT0 : (T.card : ℝ) = 0
  · have : η * N ≤ 0 := by linarith
    have hN : N = 0 := by nlinarith
    rw [hN]; simp
  have hTpos : (0 : ℝ) < T.card := lt_of_le_of_ne (by positivity) (Ne.symm hT0)
  have hMc : c * N / 4 ≤ M.card := by nlinarith
  have hsubM : M ⊆ S.filter (fun x => c / 4 * η * N ≤ (nbIn J T x).card) := by
    intro x hx
    obtain ⟨hxS, hx⟩ := Finset.mem_filter.1 hx
    refine Finset.mem_filter.2 ⟨hxS, le_trans ?_ hx⟩
    simp only [θ]; nlinarith
  have := Finset.card_le_card hsubM
  have h3 : (M.card : ℝ) ≤ (S.filter (fun x => c / 4 * η * N ≤ (nbIn J T x).card)).card := by
    exact_mod_cast this
  have : c / 4 * η * N ≤ c * N / 4 := by nlinarith
  linarith

/-- Ambos lados grandes: la conexión robusta da `e(S,T) ≥ (ρζ/8)N²`. -/
lemma cut_edges_big {J : SimpleGraph Ω} {K : Finset Ω} {c ζ ρ : ℝ} (hc : 0 < c) (hζ : 0 < ζ)
    (hζc : ζ ≤ c) (hρ : 0 < ρ) (hK : NbrClosed J K) (hrob : RobustConn J K ζ ρ)
    {S : Finset Ω} (hSK : S ⊆ K) (hS : c * Fintype.card Ω ≤ S.card)
    (hT : c * Fintype.card Ω / 2 < (K \ S).card) :
    ρ * ζ / 8 * (Fintype.card Ω : ℝ) ^ 2 ≤ ∑ x ∈ S, ((nbIn J (K \ S) x).card : ℝ) := by
  set T := K \ S
  set N : ℝ := (Fintype.card Ω : ℝ)
  have hTN : (T.card : ℝ) ≤ N := by
    show (T.card : ℝ) ≤ (Fintype.card Ω : ℝ); exact_mod_cast Finset.card_le_univ T
  have hNpos : 0 < N := by nlinarith
  have hsym : ∑ y ∈ T, ((nbIn J S y).card : ℝ) = ∑ x ∈ S, ((nbIn J T x).card : ℝ) := by
    exact_mod_cast (cut_count_symm J S T).symm
  set e := ∑ x ∈ S, ((nbIn J T x).card : ℝ)
  by_contra hlt
  push_neg at hlt
  set MS := S.filter (fun x => ρ * N < ((nbIn J T x).card : ℝ))
  set MT := T.filter (fun y => ρ * N < ((nbIn J S y).card : ℝ))
  have hMS : (MS.card : ℝ) * (ρ * N) ≤ e := by
    calc (MS.card : ℝ) * (ρ * N) = ∑ _x ∈ MS, ρ * N := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ MS, ((nbIn J T x).card : ℝ) :=
          Finset.sum_le_sum fun x hx => le_of_lt (Finset.mem_filter.1 hx).2
      _ ≤ e := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => by positivity
  have hMT : (MT.card : ℝ) * (ρ * N) ≤ e := by
    rw [← hsym]
    calc (MT.card : ℝ) * (ρ * N) = ∑ _x ∈ MT, ρ * N := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ MT, ((nbIn J S y).card : ℝ) :=
          Finset.sum_le_sum fun x hx => le_of_lt (Finset.mem_filter.1 hx).2
      _ ≤ ∑ y ∈ T, ((nbIn J S y).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => by positivity
  set M := MS ∪ MT
  have hMcard : (M.card : ℝ) < ζ * N / 4 := by
    have h1 : (M.card : ℝ) ≤ MS.card + MT.card := by exact_mod_cast Finset.card_union_le _ _
    have hρN : 0 < ρ * N := by positivity
    have h2 : (MS.card : ℝ) < ζ * N / 8 := by
      by_contra h; push_neg at h
      have : ζ * N / 8 * (ρ * N) ≤ MS.card * (ρ * N) := mul_le_mul_of_nonneg_right h hρN.le
      nlinarith
    have h3 : (MT.card : ℝ) < ζ * N / 8 := by
      by_contra h; push_neg at h
      have : ζ * N / 8 * (ρ * N) ≤ MT.card * (ρ * N) := mul_le_mul_of_nonneg_right h hρN.le
      nlinarith
    linarith
  -- aristas cruzadas entre supervivientes
  set B' : Finset (Sym2 Ω) := univ.filter (fun f => ∃ u ∈ S, ∃ w ∈ T, u ∉ M ∧ w ∉ M ∧
    J.Adj u w ∧ f = s(u, w))
  have hdisj : ∀ x, x ∈ S → x ∉ T := fun x hx hxT => (Finset.mem_sdiff.1 hxT).2 hx
  have hdegB : ∀ x, (degIn B' x : ℝ) ≤ ρ * N := by
    intro x
    by_cases hxM : x ∈ M
    · have : B'.filter (fun f => x ∈ f) = ∅ := by
        ext f
        simp only [B', Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        rintro ⟨u, hu, w, hw, huM, hwM, -, rfl⟩ hx
        rcases Sym2.mem_iff.1 hx with rfl | rfl
        · exact huM hxM
        · exact hwM hxM
      simp only [degIn, this, Finset.card_empty, Nat.cast_zero]; positivity
    by_cases hxS : x ∈ S
    · have hsub : B'.filter (fun f => x ∈ f) ⊆ (nbIn J T x).image (fun w => s(x, w)) := by
        intro f hf
        simp only [B', Finset.mem_filter, Finset.mem_univ, true_and] at hf
        obtain ⟨⟨u, hu, w, hw, -, -, huw, rfl⟩, hx⟩ := hf
        rcases Sym2.mem_iff.1 hx with rfl | rfl
        · exact Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, huw⟩, rfl⟩
        · exact absurd hw (hdisj _ hxS)
      have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
      have h2 : ¬ ρ * N < ((nbIn J T x).card : ℝ) := fun h =>
        hxM (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hxS, h⟩))
      have : (degIn B' x : ℝ) ≤ (nbIn J T x).card := by exact_mod_cast h1
      linarith [not_lt.1 h2]
    by_cases hxT : x ∈ T
    · have hsub : B'.filter (fun f => x ∈ f) ⊆ (nbIn J S x).image (fun u => s(x, u)) := by
        intro f hf
        simp only [B', Finset.mem_filter, Finset.mem_univ, true_and] at hf
        obtain ⟨⟨u, hu, w, hw, -, -, huw, rfl⟩, hx⟩ := hf
        rcases Sym2.mem_iff.1 hx with rfl | rfl
        · exact absurd hu hxS
        · exact Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨hu, huw.symm⟩, Sym2.eq_swap⟩
      have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
      have h2 : ¬ ρ * N < ((nbIn J S x).card : ℝ) := fun h =>
        hxM (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hxT, h⟩))
      have : (degIn B' x : ℝ) ≤ (nbIn J S x).card := by exact_mod_cast h1
      linarith [not_lt.1 h2]
    · have : B'.filter (fun f => x ∈ f) = ∅ := by
        ext f
        simp only [B', Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        rintro ⟨u, hu, w, hw, -, -, -, rfl⟩ hx
        rcases Sym2.mem_iff.1 hx with rfl | rfl
        · exact hxS hu
        · exact hxT hw
      simp only [degIn, this, Finset.card_empty, Nat.cast_zero]; positivity
  -- supervivientes en ambos lados
  have hSM : M.card < S.card := by
    have : (M.card : ℝ) < S.card := by nlinarith
    exact_mod_cast this
  have hTM : M.card < T.card := by
    have : (M.card : ℝ) < T.card := by nlinarith
    exact_mod_cast this
  obtain ⟨a, haS, haM⟩ := Finset.exists_mem_notMem_of_card_lt_card hSM
  obtain ⟨b, hbT, hbM⟩ := Finset.exists_mem_notMem_of_card_lt_card hTM
  have hbK : b ∈ K := (Finset.mem_sdiff.1 hbT).1
  obtain ⟨p⟩ := hrob M B' (by linarith) hdegB a (hSK haS) b hbK haM hbM
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (S : Set Ω) (by simpa using haS)
    (by simpa using (Finset.mem_sdiff.1 hbT).2)
  obtain ⟨hJ, h1M, h2M, hB⟩ := d.adj
  have hd1' : d.toProd.1 ∈ S := by simpa using hd1
  have hd2' : d.toProd.2 ∉ S := by simpa using hd2
  have hd2T : d.toProd.2 ∈ T := Finset.mem_sdiff.2 ⟨hK _ (hSK hd1') _ hJ, hd2'⟩
  exact hB (Finset.mem_filter.2 ⟨Finset.mem_univ _, _, hd1', _, hd2T, h1M, h2M, hJ, rfl⟩)

/-- Constante de expansión. -/
def expConst (c ζ ρ : ℝ) : ℝ := min (c / 4) (ρ * ζ / 16)

lemma expConst_pos {c ζ ρ : ℝ} (hc : 0 < c) (hζ : 0 < ζ) (hρ : 0 < ρ) : 0 < expConst c ζ ρ :=
  lt_min (by positivity) (by positivity)

lemma expConst_le_one {c ζ ρ : ℝ} (hc1 : c ≤ 1) : expConst c ζ ρ ≤ 1 :=
  (min_le_left _ _).trans (by linarith)

omit [Fintype Ω] in
lemma card_filter_threshold_mono (S : Finset Ω) (f : Ω → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ((S.filter (fun x => b ≤ f x)).card : ℝ) ≤ (S.filter (fun x => a ≤ f x)).card := by
  have hsub : S.filter (fun x => b ≤ f x) ⊆ S.filter (fun x => a ≤ f x) := fun x hx => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨h1, hab.trans h2⟩
  exact_mod_cast Finset.card_le_card hsub

/-- **Expansión de vértices desde la conexión robusta (S03 §§5–6).** Para todo `S ⊆ K` con
`|S| ≥ cN` y `|K ∖ S| ≥ ηN` (`0 < η ≤ 1`), al menos `κηN` vértices de `S` tienen al menos
`κηN` vecinos en `K ∖ S`, con `κ = min(c/4, ρζ/16)`. -/
theorem expansion_of_robust {J : SimpleGraph Ω} {K : Finset Ω} {c ζ ρ : ℝ} (hc : 0 < c)
    (hζ : 0 < ζ) (hζc : ζ ≤ c) (hρ : 0 < ρ) (hK : NbrClosed J K) (hdeg : MinDegOn J K c)
    (hrob : RobustConn J K ζ ρ) {S : Finset Ω} (hSK : S ⊆ K) (hS : c * Fintype.card Ω ≤ S.card)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hTη : η * Fintype.card Ω ≤ (K \ S).card) :
    expConst c ζ ρ * η * Fintype.card Ω ≤ ((S.filter (fun x =>
      expConst c ζ ρ * η * Fintype.card Ω ≤ (nbIn J (K \ S) x).card)).card : ℝ) := by
  set κ := expConst c ζ ρ
  set N : ℝ := (Fintype.card Ω : ℝ)
  have hN0 : 0 ≤ N := by positivity
  have hκ1 : κ ≤ c / 4 := min_le_left _ _
  have hκ2 : κ ≤ ρ * ζ / 16 := min_le_right _ _
  have hκ0 : 0 < κ := expConst_pos hc hζ hρ
  by_cases hTs : ((K \ S).card : ℝ) ≤ c * N / 2
  · have h := expansion_small_side hc hK hdeg hη hη1 hTη hTs
    have hle : κ * η * N ≤ c / 4 * η * N := by
      have := mul_le_mul_of_nonneg_right hκ1 (by positivity : 0 ≤ η * N)
      nlinarith
    exact hle.trans (h.trans (card_filter_threshold_mono S _ hle))
  · push_neg at hTs
    have he := cut_edges_big hc hζ hζc hρ hK hrob hSK hS hTs
    set T := K \ S
    have hTN : (T.card : ℝ) ≤ N := by
      show (T.card : ℝ) ≤ (Fintype.card Ω : ℝ); exact_mod_cast Finset.card_le_univ T
    have hSN : (S.card : ℝ) ≤ N := by
      show (S.card : ℝ) ≤ (Fintype.card Ω : ℝ); exact_mod_cast Finset.card_le_univ S
    have hNpos : 0 < N := by nlinarith
    set θ : ℝ := ρ * ζ * N / 16
    have hθ : 0 ≤ θ := by positivity
    have hsplit := sum_le_split S (fun x => ((nbIn J T x).card : ℝ)) hθ (U := N) fun x _ => by
      show ((nbIn J T x).card : ℝ) ≤ N
      exact le_trans (by exact_mod_cast card_nbIn_le_card J T x) hTN
    set M2 := S.filter (fun x => θ ≤ ((nbIn J T x).card : ℝ))
    have hM2 : ρ * ζ * N / 16 ≤ M2.card := by
      have h1 : (S.card : ℝ) * θ ≤ N * θ := mul_le_mul_of_nonneg_right hSN hθ
      have h2 : ρ * ζ / 8 * N ^ 2 ≤ M2.card * N + N * θ := by linarith
      simp only [θ] at h2
      nlinarith
    have hθκ : κ * η * N ≤ θ := by
      have := mul_le_mul_of_nonneg_right hκ2 (by positivity : 0 ≤ η * N)
      simp only [θ]; nlinarith
    calc κ * η * N ≤ θ := hθκ
      _ ≤ M2.card := hM2
      _ ≤ _ := card_filter_threshold_mono S _ hθκ

end TypedTriangle
