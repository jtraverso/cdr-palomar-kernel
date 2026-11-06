/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.HingeSupply

@[expose] public section

/-!
# A1 — Contador de bisagras con pares no diagonales y evitación de un grafo `B`

Contador propio (sin `Sym2` diagonales): un conjunto de aristas de un grafo simple con
soporte `S` es un subconjunto de `E(S)`, que tiene `C(|S|,2)` elementos. Así se conservan
las constantes `M = C(h,2)` de S02.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

omit [Fintype V] in
/-- `|E(S)| = C(|S|, 2)`: pares no diagonales de un conjunto de vértices. -/
lemma card_triEdges (S : Finset V) : (triEdges S).card = Nat.choose S.card 2 := by
  have hdiag : S.sym2.filter (fun e => e.IsDiag) = S.image (fun x => s(x, x)) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
        Finset.mem_image, Sym2.eq_iff]
      constructor
      · rintro ⟨⟨hx, -⟩, rfl⟩; exact ⟨x, hx, Or.inl ⟨rfl, rfl⟩⟩
      · rintro ⟨z, hz, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> exact ⟨⟨hz, hz⟩, rfl⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := S.sym2) (fun e => e.IsDiag)
  rw [hdiag, Finset.card_image_of_injective _ (fun x y h => by simpa using h),
    Finset.card_sym2] at hsplit
  unfold triEdges
  have : Nat.choose (S.card + 1) 2 = S.card + Nat.choose S.card 2 := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
  omega

/-- Un conjunto de aristas no diagonales está contenido en `E(soporte)`. -/
lemma subset_triEdges_support {J : Finset (Sym2 V)} (hJ : ∀ e ∈ J, ¬ e.IsDiag) :
    J ⊆ triEdges (support J) := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_triEdges]
    refine ⟨?_, ?_, fun h => hJ _ he (by simp [h])⟩ <;>
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] <;>
      exact ⟨_, he, by simp⟩

omit [Fintype V] in
lemma disjoint_of_subset_compl {R X : Finset V} [Fintype V] (hX : X ⊆ univ \ R) :
    Disjoint R X := by
  rw [Finset.disjoint_left]; intro x hxR hxX
  have := hX hxX; simp [hxR] at this

omit [Fintype V] in
lemma not_isDiag_of_mem_triEdges {T : Finset V} {e : Sym2 V} (he : e ∈ triEdges T) :
    ¬ e.IsDiag := (Finset.mem_filter.1 he).2

omit [Fintype V] in
lemma mem_of_mem_triEdges {T : Finset V} {e : Sym2 V} (he : e ∈ triEdges T) {p : V}
    (hp : p ∈ e) : p ∈ T := by
  have := (Finset.mem_filter.1 he).1
  rw [Finset.mem_sym2_iff] at this
  exact this p hp

/-- Número de conjuntos `S` de tamaño `i` que contienen un conjunto fijo `R`. -/
lemma card_supersets (R : Finset V) (i : ℕ) (hi : R.card ≤ i) :
    (univ.filter (fun S : Finset V => R ⊆ S ∧ S.card = i)).card =
      Nat.choose (Fintype.card V - R.card) (i - R.card) := by
  have heq : univ.filter (fun S : Finset V => R ⊆ S ∧ S.card = i) =
      ((univ \ R).powersetCard (i - R.card)).image (fun X => R ∪ X) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hRS, rfl⟩
      refine ⟨S \ R, ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ _) (subset_refl _), ?_⟩,
        Finset.union_sdiff_of_subset hRS⟩
      rw [Finset.card_sdiff_of_subset hRS]
    · rintro ⟨X, ⟨hX, hXc⟩, rfl⟩
      refine ⟨Finset.subset_union_left, ?_⟩
      rw [Finset.card_union_of_disjoint (disjoint_of_subset_compl hX)]; omega
  rw [heq, Finset.card_image_of_injOn, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  intro X hX Y hY hXY
  simp only [Finset.mem_coe, Finset.mem_powersetCard] at hX hY
  simp only at hXY
  rw [← Finset.union_sdiff_cancel_left (disjoint_of_subset_compl hX.1), hXY,
    Finset.union_sdiff_cancel_left (disjoint_of_subset_compl hY.1)]

/-- **Contador A1 (no diagonal).** Una familia de conjuntos de aristas no diagonales, cada
uno con soporte de tamaño exactamente `i` que contiene un conjunto fijo `R`, tiene a lo sumo
`C(n − |R|, i − |R|) · 2^{C(i,2)}` miembros. -/
theorem rooted_family_card_le (𝒥 : Finset (Finset (Sym2 V))) (R : Finset V) (i : ℕ)
    (hi : R.card ≤ i) (hdiag : ∀ J ∈ 𝒥, ∀ e ∈ J, ¬ e.IsDiag)
    (hR : ∀ J ∈ 𝒥, R ⊆ support J) (hcard : ∀ J ∈ 𝒥, (support J).card = i) :
    𝒥.card ≤ Nat.choose (Fintype.card V - R.card) (i - R.card) * 2 ^ Nat.choose i 2 := by
  set 𝒮 := univ.filter (fun S : Finset V => R ⊆ S ∧ S.card = i)
  have hmaps : ∀ J ∈ 𝒥, support J ∈ 𝒮 := fun J hJ => by
    simp [𝒮, hR J hJ, hcard J hJ]
  have h1 := Finset.card_le_mul_card_image_of_maps_to hmaps (2 ^ Nat.choose i 2) (by
    intro S hS
    have hSc : S.card = i := (Finset.mem_filter.1 hS).2.2
    have hsub : 𝒥.filter (fun J => support J = S) ⊆ (triEdges S).powerset := by
      intro J hJ
      rw [Finset.mem_filter] at hJ
      rw [Finset.mem_powerset, ← hJ.2]
      exact subset_triEdges_support (hdiag J hJ.1)
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_powerset, card_triEdges, hSc])
  rw [card_supersets R i hi] at h1
  linarith [h1]

lemma choose_le_pow_sub (n r i : ℕ) : Nat.choose (n - r) (i - r) ≤ n ^ (i - r) :=
  (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

/-- Las aristas de una bisagra no son diagonales. -/
lemma IsHinge.not_isDiag {H : Host V I} {F : Set (Multiset I)} {u v a b : V}
    {J : Finset (Sym2 V)} (hJ : IsHinge H F u v a b J) : ∀ e ∈ J, ¬ e.IsDiag := by
  intro e he
  have := hJ.1 he
  simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact H.G.not_isDiag_of_mem_edgeSet this

/-- Bisagras de orden `i` cuyo soporte contiene un conjunto `R'` ⊇ raíces. -/
theorem hinges_rooted_le {H : Host V I} {F : Set (Multiset I)} {u v a b : V}
    (i : ℕ) (R' : Finset V) (hi : R'.card ≤ i) :
    ((hinges H F u v a b i).filter (fun J => R' ⊆ support J)).card ≤
      Fintype.card V ^ (i - R'.card) * 2 ^ Nat.choose i 2 := by
  refine (rooted_family_card_le _ R' i hi ?_ ?_ ?_).trans
    (Nat.mul_le_mul_right _ (choose_le_pow_sub _ _ _))
  · intro J hJ
    simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and] at hJ
    exact hJ.1.1.not_isDiag
  · intro J hJ; exact (Finset.mem_filter.1 hJ).2
  · intro J hJ
    simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and] at hJ
    exact hJ.1.2

/-- Grado de un vértice en un conjunto de aristas `B`. -/
def degIn (B : Finset (Sym2 V)) (x : V) : ℕ := (B.filter (fun e => x ∈ e)).card

/-- Vecinos de `x` en `B`. -/
def nbrIn (B : Finset (Sym2 V)) (x : V) : Finset V := univ.filter (fun z => s(x, z) ∈ B)

lemma card_nbrIn_le (B : Finset (Sym2 V)) (x : V) : (nbrIn B x).card ≤ degIn B x := by
  unfold nbrIn degIn
  refine Finset.card_le_card_of_injOn (fun z => s(x, z)) ?_ ?_
  · intro z hz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz
    simp [hz]
  · intro z _ w _ h
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1

lemma card_le_sum_degIn (B : Finset (Sym2 V)) :
    B.card ≤ ∑ x, degIn B x := by
  have hsub : B ⊆ univ.biUnion (fun x => B.filter (fun e => x ∈ e)) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y => exact Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, by simp [he]⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- Una arista `xy` de una bisagra con ambos extremos en las raíces es `ab`. -/
lemma IsHinge.root_edge {H : Host V I} {F : Set (Multiset I)} {u v a b : V}
    {J : Finset (Sym2 V)} (hJ : IsHinge H F u v a b J) {x y : V} (hxy : s(x, y) ∈ J)
    (hx : x ∈ ({u, v, a, b} : Finset V)) (hy : y ∈ ({u, v, a, b} : Finset V)) :
    s(x, y) = s(a, b) := by
  have hnd := hJ.not_isDiag _ hxy
  have hne : x ≠ y := fun h => hnd (by simp [h])
  have hdisj := hJ.2.1
  have notin : ∀ T : Finset V, T = {u, v, a} ∨ T = {u, v, b} → x ∈ T → y ∈ T → False := by
    rintro T hT hxT hyT
    have : s(x, y) ∈ triEdges ({u, v, a} : Finset V) ∪ triEdges ({u, v, b} : Finset V) := by
      rcases hT with rfl | rfl
      · exact Finset.mem_union_left _ (mem_triEdges.2 ⟨hxT, hyT, hne⟩)
      · exact Finset.mem_union_right _ (mem_triEdges.2 ⟨hxT, hyT, hne⟩)
    exact Finset.disjoint_left.1 hdisj hxy this
  by_contra hne'
  have key : (x ∈ ({u, v, a} : Finset V) ∧ y ∈ ({u, v, a} : Finset V)) ∨
      (x ∈ ({u, v, b} : Finset V) ∧ y ∈ ({u, v, b} : Finset V)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
    rcases hx with h | h | h | h <;> rcases hy with h' | h' | h' | h' <;>
      simp_all
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact notin _ (Or.inl rfl) h1 h2
  · exact notin _ (Or.inr rfl) h1 h2

lemma mem_support_of_mem {J : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ J) {x : V}
    (hx : x ∈ e) : x ∈ support J := by
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨e, he, hx⟩

/-- **A1: bisagras robustas.** Si (H4) da `α n^{i−4}` bisagras de orden `i ≥ 6`, el historial
`Z` es un conjunto de vértices, `B` es un conjunto de aristas de grado máximo `≤ d` que no
contiene la pareja `ab`, y `(|Z| + 5d) n^{i−5} 2^{C(i,2)} ≤ (α/2) n^{i−4}`, entonces al menos
`(α/2) n^{i−4}` bisagras de orden `i` evitan `Z` fuera de las raíces y son disjuntas de `B`.
Las aristas entre raíces distintas de `ab` están excluidas por la definición de bisagra. -/
theorem robust_fresh_hinges {H : Host V I} {F : Set (Multiset I)} {u v a b : V} (hab : a ≠ b)
    (hTa : IsAllowed H F {u, v, a}) (hTb : IsAllowed H F {u, v, b}) (i : ℕ) (hi : 6 ≤ i)
    (α : ℝ) (Z : Finset V) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hB : s(a, b) ∉ B)
    (hsupply : α * (Fintype.card V : ℝ) ^ (i - 4) ≤ (hinges H F u v a b i).card)
    (hwin : ((Z.card : ℝ) + 5 * d) * (Fintype.card V : ℝ) ^ (i - 5) * 2 ^ Nat.choose i 2 ≤
      α / 2 * (Fintype.card V : ℝ) ^ (i - 4)) :
    α / 2 * (Fintype.card V : ℝ) ^ (i - 4) ≤
      ((hinges H F u v a b i).filter (fun J =>
        (∀ z ∈ Z, z ∈ support J → z ∈ ({u, v, a, b} : Finset V)) ∧ Disjoint J B)).card := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := distinct_of_card_three hTb.1
  set R : Finset V := {u, v, a, b} with hRdef
  have hR := roots_card huv hua hva hub hvb hab
  set K := hinges H F u v a b i
  set n := Fintype.card V
  set M := 2 ^ Nat.choose i 2
  have hKmem : ∀ J ∈ K, IsHinge H F u v a b J ∧ R ⊆ support J := fun J hJ => by
    simp only [K, hinges, Finset.mem_filter, Finset.mem_univ, true_and] at hJ
    exact ⟨hJ.1, (hinge_order_ge_six hab hTa hTb hJ.1).1⟩
  set Zout := Z.filter (fun z => z ∉ R)
  set Z1 := (R.biUnion (nbrIn B)).filter (fun z => z ∉ R)
  set B' := B.filter (fun e => ¬ e.IsDiag ∧ ∀ y ∈ e, y ∉ R)
  set X1 := Zout.biUnion (fun z => K.filter (fun J => insert z R ⊆ support J))
  set X2 := Z1.biUnion (fun z => K.filter (fun J => insert z R ⊆ support J))
  set X3 := B'.biUnion (fun e => K.filter (fun J => R ∪ e.toFinset ⊆ support J))
  have hbad : K.filter (fun J => ¬ ((∀ z ∈ Z, z ∈ support J → z ∈ R) ∧ Disjoint J B)) ⊆
      X1 ∪ X2 ∪ X3 := by
    intro J hJ
    rw [Finset.mem_filter] at hJ
    obtain ⟨hJK, hbadJ⟩ := hJ
    obtain ⟨hJh, hRJ⟩ := hKmem J hJK
    rw [not_and_or] at hbadJ
    rcases hbadJ with h | h
    · push_neg at h
      obtain ⟨z, hzZ, hzJ, hzR⟩ := h
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.2
        ⟨z, Finset.mem_filter.2 ⟨hzZ, hzR⟩, Finset.mem_filter.2 ⟨hJK, ?_⟩⟩))
      exact Finset.insert_subset hzJ hRJ
    · rw [Finset.not_disjoint_iff] at h
      obtain ⟨e, heJ, heB⟩ := h
      induction e using Sym2.ind with
      | _ x y =>
      have hxJ : x ∈ support J := mem_support_of_mem heJ (by simp)
      have hyJ : y ∈ support J := mem_support_of_mem heJ (by simp)
      by_cases hx : x ∈ R <;> by_cases hy : y ∈ R
      · exact absurd (hJh.root_edge heJ hx hy ▸ heB) hB
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.2
          ⟨y, Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨x, hx, ?_⟩, hy⟩,
            Finset.mem_filter.2 ⟨hJK, Finset.insert_subset hyJ hRJ⟩⟩))
        simp [nbrIn, heB]
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.2
          ⟨x, Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨y, hy, ?_⟩, hx⟩,
            Finset.mem_filter.2 ⟨hJK, Finset.insert_subset hxJ hRJ⟩⟩))
        simp [nbrIn, Sym2.eq_swap, heB]
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.2
          ⟨s(x, y), Finset.mem_filter.2 ⟨heB, hJh.not_isDiag _ heJ, ?_⟩,
            Finset.mem_filter.2 ⟨hJK, Finset.union_subset hRJ ?_⟩⟩)
        · intro w hw; simp only [Sym2.mem_iff] at hw; rcases hw with rfl | rfl <;> assumption
        · intro w hw; simp only [Sym2.mem_toFinset, Sym2.mem_iff] at hw
          rcases hw with rfl | rfl <;> assumption
  -- cotas de cada familia
  have hthrough : ∀ z ∉ R, (K.filter (fun J => insert z R ⊆ support J)).card ≤
      n ^ (i - 5) * M := fun z hz => by
    have h := hinges_rooted_le (H := H) (F := F) (u := u) (v := v) (a := a) (b := b) i
      (insert z R) (by rw [Finset.card_insert_of_notMem hz, hR]; omega)
    rwa [Finset.card_insert_of_notMem hz, hR] at h
  have htwo : ∀ e ∈ B', (K.filter (fun J => R ∪ e.toFinset ⊆ support J)).card ≤
      n ^ (i - 6) * M := fun e he => by
    rw [Finset.mem_filter] at he
    have hdj : Disjoint R e.toFinset := by
      rw [Finset.disjoint_left]; intro w hwR hwe
      rw [Sym2.mem_toFinset] at hwe
      exact he.2.2 w hwe hwR
    have hc : (R ∪ e.toFinset).card = 6 := by
      rw [Finset.card_union_of_disjoint hdj, hR, Sym2.card_toFinset_of_not_isDiag e he.2.1]
    have h := hinges_rooted_le (H := H) (F := F) (u := u) (v := v) (a := a) (b := b) i
      (R ∪ e.toFinset) (by omega)
    rwa [hc] at h
  have hX1 : X1.card ≤ Z.card * (n ^ (i - 5) * M) := by
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum fun z hz => hthrough z (Finset.mem_filter.1 hz).2).trans ?_
    rw [Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
  have hZ1 : Z1.card ≤ 4 * d := by
    refine (Finset.card_filter_le _ _).trans (Finset.card_biUnion_le.trans ?_)
    refine (Finset.sum_le_sum fun x _ => (card_nbrIn_le B x).trans (hdeg x)).trans ?_
    rw [Finset.sum_const, smul_eq_mul, hR]
  have hX2 : X2.card ≤ 4 * d * (n ^ (i - 5) * M) := by
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum fun z hz => hthrough z (Finset.mem_filter.1 hz).2).trans ?_
    rw [Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hZ1
  have hB' : B'.card ≤ n * d := by
    refine (Finset.card_filter_le _ _).trans ((card_le_sum_degIn B).trans ?_)
    refine (Finset.sum_le_sum fun x _ => hdeg x).trans ?_
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
  have hX3 : X3.card ≤ n * d * (n ^ (i - 6) * M) := by
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum fun e he => htwo e he).trans ?_
    rw [Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hB'
  have hpow : n ^ (i - 5) = n * n ^ (i - 6) := by
    rw [← pow_succ']; congr 1; omega
  have hbadcard : ((K.filter (fun J => ¬ ((∀ z ∈ Z, z ∈ support J → z ∈ R) ∧
      Disjoint J B))).card : ℝ) ≤ ((Z.card : ℝ) + 5 * d) * (n : ℝ) ^ (i - 5) * M := by
    have h1 := (Finset.card_le_card hbad).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have h2 : (K.filter (fun J => ¬ ((∀ z ∈ Z, z ∈ support J → z ∈ R) ∧
        Disjoint J B))).card ≤ (Z.card + 5 * d) * n ^ (i - 5) * M := by
      have : Z.card * (n ^ (i - 5) * M) + 4 * d * (n ^ (i - 5) * M) +
          n * d * (n ^ (i - 6) * M) = (Z.card + 5 * d) * n ^ (i - 5) * M := by
        rw [hpow]; ring
      omega
    exact_mod_cast h2
  have hsplit := Finset.card_filter_add_card_filter_not (s := K)
    (fun J => (∀ z ∈ Z, z ∈ support J → z ∈ R) ∧ Disjoint J B)
  have hsplit' : ((K.filter (fun J => (∀ z ∈ Z, z ∈ support J → z ∈ R) ∧
      Disjoint J B)).card : ℝ) + (K.filter (fun J => ¬ ((∀ z ∈ Z, z ∈ support J → z ∈ R) ∧
      Disjoint J B))).card = K.card := by exact_mod_cast hsplit
  have hM : (M : ℝ) = 2 ^ Nat.choose i 2 := by simp [M]
  rw [hM] at hbadcard
  linarith

end TypedTriangle
