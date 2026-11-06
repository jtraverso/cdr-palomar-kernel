/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SparseEdgeDefs

@[expose] public section

/-!
# Retículo físico bajo borrado disperso de aristas (V9, prioridad 1)

Resultado S17 (`dossier/g3_terminal_20261022/ELIMINACION_DISPERSA.md`, (1.1)) para los hosts
físicos, a partir SÓLO de (H3) y (H4):

existen `η > 0` y `n₀`, que dependen sólo de `α` y `h` (fijados antes del host y de `B`),
tales que para todo host de orden `n ≥ n₀` con (H3) y (H4) y todo `B` con `Δ(B) ≤ η n`,

    Λ_(H−B) = Λ_H ∩ {x : x_e = 0 para toda e ∈ B}.

`H − B` es `subHost H ((edges H) \ B)`: grafo `fromEdgeSet ((edges H) \ B) ⊓ H.G`, mismas
etiquetas. La equivalencia de soporte ambiente (`zeroOn` frente a `supportedOn`) se prueba
en `lattice_inf_zeroOn_eq_inf_supportedOn`.

## Autocontención y adaptador

Este archivo depende sólo de `SparseEdgeDefs.lean`, que importa sólo Mathlib. Las
definiciones del contrato (`triEdges`, `edges`,
`IsAllowed`, `IsDecomposition`, `ind`, `lattice`, `commonNbrs`, `CommonNbrCond`, `support`,
`wedge`, `IsHinge`, `hinges`, `HingeCond`, `degIn`, `nbrIn`) se escriben en `SparseEdgeDefs.lean` con los mismos
cuerpos que en `Defs.lean`/`RobustHinge.lean`, pero con el host desplegado en `(G, lab)`.
Con `G := H.G`, `lab := H.lab` coinciden por definición con las de `TypedTriangle`
(`lattice H F`, `CommonNbrCond H F α`, `HingeCond H F α h`), y `subGraph H.G K` es el grafo de
`subHost H K`. El adaptador (una línea `rfl`/`Iff.rfl` por definición y el corolario con
`Host`) está esbozado en `FORMALIZATION_STATUS.md` §4septies; NO se compiló en esta ronda,
porque este entorno no compila las fuentes recibidas.

## Prueba

No se usan matchings: se borra una arista `e ∈ B` cada vez. En la etapa con `B₀ ⊆ B` ya
borrado, para `x ∈ Λ_(H−B₀)` con `x_e = 0` se aplica el endomorfismo lineal
`y ↦ y − y_e · χ_(T₀)` (`T₀` un triángulo de `H − B₀` que contiene `e`), que lleva cada
generador de `Λ_(H−B₀)` a `Λ_(H−B₀−e)` gracias a la diferencia de pivotes
`χ_T − χ_(T₀) ∈ Λ_(H−B₀−e)` (dos bisagras de (H4) que evitan TODO `B`, a través de un
ápice fresco de (H3)), y fija `x`. Todas las coordenadas de `x` se conservan; la prueba es
de pertenencia entera exacta, sin saturación racional. No se da ninguna cota de norma:
este resultado NO es una compresión uniforme.

No se usan (H1), (H2), tipicidad, rango acotado, semilla tras el borrado ni finitud de
etiquetas; `B ⊆ E(H)` tampoco es necesario.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle.SparseEdge

variable {V I : Type*} [Fintype V]

/-! ### Conteo de conjuntos de aristas con soporte anclado -/

omit [Fintype V] in
lemma card_triEdges (S : Finset V) : (triEdges S).card = S.card.choose 2 := by
  rw [← Sym2.card_image_offDiag]
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ x y =>
  simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff, mem_image, mem_offDiag]
  constructor
  · rintro ⟨⟨hx, hy⟩, hxy⟩
    exact ⟨(x, y), ⟨hx, hy, hxy⟩, rfl⟩
  · rintro ⟨⟨p, q⟩, ⟨hp, hq, hpq⟩, he⟩
    change s(p, q) = s(x, y) at he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨hp, hq⟩, hpq⟩
    · exact ⟨⟨hq, hp⟩, Ne.symm hpq⟩

lemma subset_triEdges_support {J : Finset (Sym2 V)} (hJ : ∀ e ∈ J, ¬ e.IsDiag) :
    J ⊆ triEdges (support J) := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
  refine mem_triEdges.2 ⟨mem_support_of_mem he (by simp), mem_support_of_mem he (by simp), ?_⟩
  intro hxy
  exact hJ _ he (by simp [hxy])

/-- Conjuntos de aristas no diagonales con soporte de tamaño `i` que contiene `P`. -/
def pinned (P : Finset V) (i : ℕ) : Finset (Finset (Sym2 V)) :=
  univ.filter (fun J => (support J).card = i ∧ P ⊆ support J ∧ ∀ e ∈ J, ¬ e.IsDiag)

/-- Supraconjuntos de `P` de tamaño `i`: a lo sumo `n^(i - |P|)`. -/
lemma card_supersets_le (P : Finset V) (i : ℕ) :
    (univ.filter (fun S : Finset V => S.card = i ∧ P ⊆ S)).card ≤
      Fintype.card V ^ (i - P.card) := by
  calc (univ.filter (fun S : Finset V => S.card = i ∧ P ⊆ S)).card
      ≤ (powersetCard (i - P.card) (univ : Finset V)).card := by
        refine Finset.card_le_card_of_injOn (fun S => S \ P) ?_ ?_
        · intro S hS
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hS
          rw [Finset.mem_coe, mem_powersetCard]
          exact ⟨subset_univ _, by rw [Finset.card_sdiff_of_subset hS.2, hS.1]⟩
        · intro S hS T hT hST
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hS hT
          have h1 := Finset.sdiff_union_of_subset hS.2
          have h2 := Finset.sdiff_union_of_subset hT.2
          simp only at hST
          rw [← h1, ← h2, hST]
    _ = (Fintype.card V).choose (i - P.card) := by rw [card_powersetCard, card_univ]
    _ ≤ Fintype.card V ^ (i - P.card) := Nat.choose_le_pow _ _

lemma card_pinned_le (P : Finset V) (i k : ℕ) (hk : k ≤ P.card) (hn : 1 ≤ Fintype.card V) :
    (pinned P i).card ≤ 2 ^ i.choose 2 * Fintype.card V ^ (i - k) := by
  set Ss := univ.filter (fun S : Finset V => S.card = i ∧ P ⊆ S)
  have hsub : pinned P i ⊆ Ss.biUnion (fun S => (triEdges S).powerset) := by
    intro J hJ
    simp only [pinned, mem_filter, mem_univ, true_and] at hJ
    refine Finset.mem_biUnion.2 ⟨support J, ?_, Finset.mem_powerset.2
      (subset_triEdges_support hJ.2.2)⟩
    simp only [Ss, mem_filter, mem_univ, true_and]
    exact ⟨hJ.1, hJ.2.1⟩
  calc (pinned P i).card ≤ (Ss.biUnion (fun S => (triEdges S).powerset)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ S ∈ Ss, ((triEdges S).powerset).card := Finset.card_biUnion_le
    _ = ∑ S ∈ Ss, 2 ^ i.choose 2 := by
        refine Finset.sum_congr rfl fun S hS => ?_
        simp only [Ss, mem_filter, mem_univ, true_and] at hS
        rw [card_powerset, card_triEdges, hS.1]
    _ = Ss.card * 2 ^ i.choose 2 := by rw [sum_const, smul_eq_mul]
    _ ≤ Fintype.card V ^ (i - k) * 2 ^ i.choose 2 := by
        refine Nat.mul_le_mul_right _ ?_
        by_cases hPi : P.card ≤ i
        · exact (card_supersets_le P i).trans (Nat.pow_le_pow_right hn (by omega))
        · have : Ss = ∅ := by
            refine Finset.filter_eq_empty_iff.2 fun S _ hS => hPi ?_
            exact hS.1 ▸ Finset.card_le_card hS.2
          simp [this]
    _ = 2 ^ i.choose 2 * Fintype.card V ^ (i - k) := Nat.mul_comm _ _

lemma card_nbrIn_le (B : Finset (Sym2 V)) (x : V) : (nbrIn B x).card ≤ degIn B x := by
  refine Finset.card_le_card_of_injOn (fun z => s(x, z)) ?_ ?_
  · intro z hz
    simp only [nbrIn, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hz
    simp only [coe_filter, Set.mem_setOf_eq]
    exact ⟨hz, by simp⟩
  · intro z _ w _ hzw
    simp only [Sym2.eq_iff] at hzw
    rcases hzw with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1

lemma card_le_sum_degIn (B : Finset (Sym2 V)) :
    B.card ≤ ∑ x, degIn B x := by
  have : B ⊆ univ.biUnion (fun x => B.filter (fun e => x ∈ e)) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y => exact Finset.mem_biUnion.2 ⟨x, mem_univ _, mem_filter.2 ⟨he, by simp⟩⟩
  exact (Finset.card_le_card this).trans Finset.card_biUnion_le

/-! ### Bisagras robustas que evitan un conjunto disperso `B` -/

omit [Fintype V] in
/-- Una arista no diagonal con extremos en `{u,v,a,b}`, distinta de `ab`, está en
`E(uva) ∪ E(uvb)`. -/
lemma mem_triEdges_union_of_roots {u v a b x y : V} (hxy : x ≠ y)
    (hx : x ∈ ({u, v, a, b} : Finset V)) (hy : y ∈ ({u, v, a, b} : Finset V))
    (hab : s(x, y) ≠ s(a, b)) :
    s(x, y) ∈ triEdges {u, v, a} ∪ triEdges {u, v, b} := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rw [Finset.mem_union, mem_triEdges, mem_triEdges]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hxy
    | exact absurd rfl hab
    | exact absurd (Sym2.eq_swap) hab
    | (left; exact ⟨by tauto, by tauto, hxy⟩)
    | (right; exact ⟨by tauto, by tauto, hxy⟩)

/-- **Bisagra que evita `B`.** De (H4): si `ab ∉ B`, `Δ(B) ≤ d` y `5 d 2^C(h,2) < α n`,
existe una bisagra para `(uva, uvb)` disjunta de `B`. -/
theorem exists_hinge_avoiding {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hH4 : HingeCond G lab F α h) {u v a b : V} (hab : a ≠ b)
    (hTa : IsAllowed G lab F {u, v, a}) (hTb : IsAllowed G lab F {u, v, b})
    (B : Finset (Sym2 V)) (d : ℝ) (hdeg : ∀ x, (degIn B x : ℝ) ≤ d) (hB : s(a, b) ∉ B)
    (hwin : 5 * d * 2 ^ h.choose 2 < α * Fintype.card V) :
    ∃ J, IsHinge G lab F u v a b J ∧ Disjoint J B := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := distinct_of_card_three hTb.1
  have hn1 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨u⟩
  have hd0 : 0 ≤ d := le_trans (Nat.cast_nonneg _) (hdeg u)
  obtain ⟨i, hi6, hih, hsupply⟩ := hH4 u v a b hab hTa hTb
  by_contra hcon
  push_neg at hcon
  set R : Finset V := {u, v, a, b} with hR
  have hR4 : R.card = 4 := by
    rw [hR, Finset.card_insert_of_notMem (by simp [huv, hua, hub]),
      Finset.card_insert_of_notMem (by simp [hva, hvb]),
      Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
  set P : Sym2 V → Finset V := fun f => R ∪ univ.filter (fun x => x ∈ f) with hP
  set B1 := B.filter (fun f => (∃ r ∈ R, r ∈ f) ∧ ∃ x ∈ f, x ∉ R) with hB1
  set B2 := B.filter (fun f => ¬ f.IsDiag ∧ ∀ x ∈ f, x ∉ R) with hB2
  have hcover : hinges G lab F u v a b i ⊆
      B1.biUnion (fun f => pinned (P f) i) ∪ B2.biUnion (fun f => pinned (P f) i) := by
    intro J hJ
    simp only [hinges, mem_filter, mem_univ, true_and] at hJ
    obtain ⟨hJh, hJi⟩ := hJ
    obtain ⟨f, hfJ, hfB⟩ := Finset.not_disjoint_iff.1 (hcon J hJh)
    have hfnd : ¬ f.IsDiag := not_isDiag_of_mem_edges (hJh.1 hfJ)
    have hJnd : ∀ e ∈ J, ¬ e.IsDiag := fun e he => not_isDiag_of_mem_edges (hJh.1 he)
    have hpin : J ∈ pinned (P f) i := by
      simp only [pinned, mem_filter, mem_univ, true_and]
      refine ⟨hJi, Finset.union_subset (hJh.roots_subset_support huv hua hva hub hvb) ?_, hJnd⟩
      intro x hx
      exact mem_support_of_mem hfJ (Finset.mem_filter.1 hx).2
    by_cases hout : ∃ x ∈ f, x ∉ R
    · by_cases hin : ∃ r ∈ R, r ∈ f
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.2
          ⟨f, Finset.mem_filter.2 ⟨hfB, hin, hout⟩, hpin⟩)
      · push_neg at hin
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2
          ⟨f, Finset.mem_filter.2 ⟨hfB, hfnd, fun x hx hxR => hin x hxR hx⟩, hpin⟩)
    · push_neg at hout
      exfalso
      induction f using Sym2.ind with
      | _ x y =>
      have hxy : x ≠ y := fun h => hfnd (by simp [h])
      have hne : s(x, y) ≠ s(a, b) := fun h => hB (h ▸ hfB)
      exact Finset.disjoint_left.1 hJh.2.1 hfJ
        (mem_triEdges_union_of_roots hxy (hout x (by simp)) (hout y (by simp)) hne)
  -- cotas de `|B1|`, `|B2|`
  have hB1card : (B1.card : ℝ) ≤ 4 * d := by
    have hsub : B1 ⊆ R.biUnion (fun r => B.filter (fun e => r ∈ e)) := by
      intro f hf
      obtain ⟨hfB, ⟨r, hr, hrf⟩, -⟩ := Finset.mem_filter.1 hf
      exact Finset.mem_biUnion.2 ⟨r, hr, Finset.mem_filter.2 ⟨hfB, hrf⟩⟩
    have h1 : B1.card ≤ ∑ r ∈ R, degIn B r :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    calc (B1.card : ℝ) ≤ ∑ r ∈ R, (degIn B r : ℝ) := by exact_mod_cast h1
      _ ≤ ∑ _r ∈ R, d := Finset.sum_le_sum fun r _ => hdeg r
      _ = 4 * d := by rw [sum_const, hR4]; simp
  have hB2card : (B2.card : ℝ) ≤ Fintype.card V * d := by
    have h1 : B2.card ≤ ∑ x, degIn B x :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (card_le_sum_degIn B)
    calc (B2.card : ℝ) ≤ ∑ x, (degIn B x : ℝ) := by exact_mod_cast h1
      _ ≤ ∑ _x : V, d := Finset.sum_le_sum fun x _ => hdeg x
      _ = Fintype.card V * d := by simp
  -- cotas por arista
  set n : ℕ := Fintype.card V with hn
  set c : ℕ := 2 ^ i.choose 2 with hc
  have hP1 : ∀ f ∈ B1, (pinned (P f) i).card ≤ c * n ^ (i - 5) := by
    intro f hf
    obtain ⟨-, -, x, hxf, hxR⟩ := Finset.mem_filter.1 hf
    refine card_pinned_le _ _ _ ?_ hn1
    have hsub : insert x R ⊆ P f := by
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨mem_univ _, hxf⟩)
      · exact Finset.mem_union_left _ hy
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hxR, hR4] at this
    exact this
  have hP2 : ∀ f ∈ B2, (pinned (P f) i).card ≤ c * n ^ (i - 6) := by
    intro f hf
    obtain ⟨-, hfnd, hfR⟩ := Finset.mem_filter.1 hf
    refine card_pinned_le _ _ _ ?_ hn1
    induction f using Sym2.ind with
    | _ x y =>
    have hxy : x ≠ y := fun h => hfnd (by simp [h])
    have hxR := hfR x (by simp)
    have hyR := hfR y (by simp)
    have hsub : insert x (insert y R) ⊆ P s(x, y) := by
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨mem_univ _, by simp⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨mem_univ _, by simp⟩)
      · exact Finset.mem_union_left _ hz
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxR]), Finset.card_insert_of_notMem hyR,
      hR4] at this
    exact this
  have hcardH : ((hinges G lab F u v a b i).card : ℝ) ≤
      B1.card * (c * n ^ (i - 5)) + B2.card * (c * n ^ (i - 6)) := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le (B1.biUnion (fun f => pinned (P f) i))
      (B2.biUnion (fun f => pinned (P f) i))
    have h3 : (B1.biUnion (fun f => pinned (P f) i)).card ≤ B1.card * (c * n ^ (i - 5)) := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ f ∈ B1, (pinned (P f) i).card ≤ ∑ _f ∈ B1, c * n ^ (i - 5) :=
            Finset.sum_le_sum hP1
        _ = B1.card * (c * n ^ (i - 5)) := by rw [sum_const, smul_eq_mul]
    have h4 : (B2.biUnion (fun f => pinned (P f) i)).card ≤ B2.card * (c * n ^ (i - 6)) := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ f ∈ B2, (pinned (P f) i).card ≤ ∑ _f ∈ B2, c * n ^ (i - 6) :=
            Finset.sum_le_sum hP2
        _ = B2.card * (c * n ^ (i - 6)) := by rw [sum_const, smul_eq_mul]
    have : (hinges G lab F u v a b i).card ≤
        B1.card * (c * n ^ (i - 5)) + B2.card * (c * n ^ (i - 6)) := by omega
    exact_mod_cast this
  -- aritmética final
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpow5 : (n : ℝ) ^ (i - 5) = n * (n : ℝ) ^ (i - 6) := by
    rw [← pow_succ']; congr 1; omega
  have hpow4 : (n : ℝ) ^ (i - 4) = n * (n : ℝ) ^ (i - 5) := by
    rw [← pow_succ']; congr 1; omega
  have hcR : (c : ℝ) ≤ 2 ^ h.choose 2 := by
    rw [hc]; push_cast
    exact pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hih)
  have hq6 : (0 : ℝ) ≤ (n : ℝ) ^ (i - 6) := by positivity
  have hq5 : (0 : ℝ) < (n : ℝ) ^ (i - 5) := by positivity
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hbad : ((hinges G lab F u v a b i).card : ℝ) ≤ 5 * d * c * (n : ℝ) ^ (i - 5) := by
    refine hcardH.trans ?_
    have e1 : (B1.card : ℝ) * (c * (n : ℝ) ^ (i - 5)) ≤ 4 * d * (c * (n : ℝ) ^ (i - 5)) :=
      mul_le_mul_of_nonneg_right hB1card (by positivity)
    have e2 : (B2.card : ℝ) * (c * (n : ℝ) ^ (i - 6)) ≤
        (n * d) * (c * (n : ℝ) ^ (i - 6)) :=
      mul_le_mul_of_nonneg_right hB2card (by positivity)
    have : (n * d) * (c * (n : ℝ) ^ (i - 6)) = d * c * (n : ℝ) ^ (i - 5) := by
      rw [hpow5]; ring
    nlinarith
  have hlt : 5 * d * c * (n : ℝ) ^ (i - 5) < α * (n : ℝ) ^ (i - 4) := by
    rw [hpow4]
    have : 5 * d * c ≤ 5 * d * 2 ^ h.choose 2 :=
      mul_le_mul_of_nonneg_left hcR (by positivity)
    have := lt_of_le_of_lt this hwin
    calc 5 * d * c * (n : ℝ) ^ (i - 5) < α * n * (n : ℝ) ^ (i - 5) :=
          mul_lt_mul_of_pos_right this hq5
      _ = α * (n * (n : ℝ) ^ (i - 5)) := by ring
  linarith

/-! ### Ápice fresco desde (H3) -/

omit [Fintype V] in
lemma map_lab_triple (lab : V → I) {u v a : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) :
    ({u, v, a} : Finset V).val.map lab = {lab u, lab v, lab a} := by
  rw [Finset.insert_val_of_notMem (by simp [huv, hua]),
    Finset.insert_val_of_notMem (by simp [hva])]
  simp

/-- **Ápice fresco.** De (H3): si `|X| < α n`, existe `t ∉ X` con `uvt` permitido. -/
lemma exists_fresh_apex {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond G lab F α) {u v a : V} (hTa : IsAllowed G lab F {u, v, a})
    (X : Finset V) (hX : (X.card : ℝ) < α * Fintype.card V) :
    ∃ t, IsAllowed G lab F {u, v, t} ∧ t ∉ X := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  have hF : ({lab u, lab v, lab a} : Multiset I) ∈ F := by
    have := hTa.2.2
    rwa [map_lab_triple lab huv hua hva] at this
  have hlt : X.card < (commonNbrs G lab (lab a) u v).card := by
    exact_mod_cast hX.trans_le (hH3 u v huv (lab a) hF)
  obtain ⟨t, ht, htX⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  obtain ⟨hut, hvt, hlab⟩ := ht
  have hut' : u ≠ t := hut.ne
  have hvt' : v ≠ t := hvt.ne
  refine ⟨t, ⟨card_three_of_distinct huv hut' hvt', ?_, ?_⟩, htX⟩
  · have huvadj : G.Adj u v := hTa.2.1 u (by simp) v (by simp) huv
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | assumption | exact SimpleGraph.Adj.symm ‹_›
  · rw [map_lab_triple lab huv hut' hvt', hlab]
    exact hF

/-! ### Paso de una arista: reescritura lineal por un pivote -/

/-- **Paso de borrado de una arista (abstracto).** Si para algún `T₀` cada triángulo `T`
de `G − (E∖K)` que contiene `e` cumple `χ_T − χ_(T₀) ∈ Λ_(K∖e)`, entonces todo
`x ∈ Λ_K` con `x_e = 0` está en `Λ_(K∖e)`: se aplica `y ↦ y − y_e · χ_(T₀)`, que lleva
`Λ_K` a `Λ_(K∖e)` y fija `x`. -/
theorem mem_lattice_erase_of_pivot {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {K : Finset (Sym2 V)} {e : Sym2 V} (T₀ : Finset V)
    (hpiv : ∀ T, IsAllowed (subGraph G K) lab F T → e ∈ triEdges T →
      ind (triEdges T) - ind (triEdges T₀) ∈ lattice (subGraph G (K.erase e)) lab F)
    {x : Sym2 V → ℤ} (hx : x ∈ lattice (subGraph G K) lab F) (hxe : x e = 0) :
    x ∈ lattice (subGraph G (K.erase e)) lab F := by
  set φ : (Sym2 V → ℤ) →ₗ[ℤ] (Sym2 V → ℤ) :=
    LinearMap.id - (LinearMap.proj e).smulRight (ind (triEdges T₀)) with hφ
  have hφapp : ∀ y, φ y = y - y e • ind (triEdges T₀) := fun y => rfl
  have hle : lattice (subGraph G K) lab F ≤
      (lattice (subGraph G (K.erase e)) lab F).comap φ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨T, hT, rfl⟩
    change φ (ind (triEdges T)) ∈ lattice (subGraph G (K.erase e)) lab F
    rw [hφapp]
    by_cases heT : e ∈ triEdges T
    · have : ind (triEdges T) e = 1 := by simp [ind, heT]
      rw [this, one_smul]
      exact hpiv T hT heT
    · have : ind (triEdges T) e = 0 := by simp [ind, heT]
      rw [this, zero_smul, sub_zero]
      refine ind_mem_lattice (isAllowed_subGraph_iff.2 ⟨(isAllowed_subGraph_iff.1 hT).1, ?_⟩)
      intro f hf
      exact Finset.mem_erase.2 ⟨fun h => heT (h ▸ hf), (isAllowed_subGraph_iff.1 hT).2 hf⟩
  have := hle hx
  rw [Submodule.mem_comap, hφapp, hxe, zero_smul, sub_zero] at this
  exact this

omit [Fintype V] in
lemma sdiff_erase_eq (E B₀ : Finset (Sym2 V)) (e : Sym2 V) :
    (E \ B₀).erase e = E \ insert e B₀ := by
  ext f
  simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, not_or]
  tauto

/-- **Borrado de `B` dado un proveedor de pivotes (abstracto).** Se usa sólo como paso
interno: el proveedor se construye desde (H3)–(H4) en `pivot_diff_mem`. -/
theorem lattice_inf_zeroOn_le_of_pivots {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} (B : Finset (Sym2 V))
    (hpiv : ∀ B₀ ⊆ B, ∀ e ∈ B, e ∉ B₀ → ∃ T₀ : Finset V, ∀ T,
      IsAllowed (subGraph G (edges G \ B₀)) lab F T → e ∈ triEdges T →
      ind (triEdges T) - ind (triEdges T₀) ∈
        lattice (subGraph G ((edges G \ B₀).erase e)) lab F) :
    lattice G lab F ⊓ zeroOn B ≤ lattice (subGraph G (edges G \ B)) lab F := by
  suffices key : ∀ B₀ : Finset (Sym2 V), B₀ ⊆ B → ∀ x ∈ lattice G lab F,
      (∀ e ∈ B₀, x e = 0) → x ∈ lattice (subGraph G (edges G \ B₀)) lab F by
    intro x hx
    rw [Submodule.mem_inf] at hx
    exact key B (Finset.Subset.refl B) x hx.1 hx.2
  intro B₀
  induction B₀ using Finset.induction_on with
  | empty =>
    intro _ x hx _
    rw [Finset.sdiff_empty, lattice_subGraph_edges]
    exact hx
  | insert e B₀ heB₀ ih =>
    intro hsub x hx hxz
    have hB₀ : B₀ ⊆ B := (Finset.subset_insert _ _).trans hsub
    have heB : e ∈ B := hsub (Finset.mem_insert_self _ _)
    have hx₀ := ih hB₀ x hx (fun f hf => hxz f (Finset.mem_insert_of_mem hf))
    obtain ⟨T₀, hT₀⟩ := hpiv B₀ hB₀ e heB heB₀
    have := mem_lattice_erase_of_pivot T₀ hT₀ hx₀ (hxz e (Finset.mem_insert_self _ _))
    rwa [sdiff_erase_eq] at this

/-! ### Diferencia de pivotes en el host físico, desde (H3)–(H4) -/

/-- **Diferencia de pivotes física.** Con las ventanas `2 + 4d < α n` y
`5 d 2^C(h,2) < α n` (verificadas una sola vez en el host original), para `B₀ ⊆ B` y dos
triángulos `T`, `T₀` de `H − B₀` que contienen `e`, `χ_T − χ_(T₀) ∈ Λ_(H − B₀ − e)`.
Se pasa por un ápice fresco `t` de (H3) y dos bisagras de (H4) que evitan TODO `B`. -/
theorem pivot_diff_mem {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hH3 : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h)
    (B : Finset (Sym2 V)) (d : ℝ) (hdeg : ∀ x, (degIn B x : ℝ) ≤ d)
    (hwin1 : 2 + 4 * d < α * Fintype.card V)
    (hwin2 : 5 * d * 2 ^ h.choose 2 < α * Fintype.card V)
    {B₀ : Finset (Sym2 V)} (hB₀ : B₀ ⊆ B) {e : Sym2 V} {T T₀ : Finset V}
    (hT : IsAllowed (subGraph G (edges G \ B₀)) lab F T)
    (hT₀ : IsAllowed (subGraph G (edges G \ B₀)) lab F T₀)
    (heT : e ∈ triEdges T) (heT₀ : e ∈ triEdges T₀) :
    ind (triEdges T) - ind (triEdges T₀) ∈
      lattice (subGraph G ((edges G \ B₀).erase e)) lab F := by
  induction e using Sym2.ind with
  | _ u v =>
  obtain ⟨hu, hv, huv⟩ := mem_triEdges.1 heT
  obtain ⟨hu₀, hv₀, -⟩ := mem_triEdges.1 heT₀
  obtain ⟨hTG, hTK⟩ := isAllowed_subGraph_iff.1 hT
  obtain ⟨hT₀G, -⟩ := isAllowed_subGraph_iff.1 hT₀
  obtain ⟨a, hau, hav, rfl⟩ := eq_triple_of_mem hTG.1 hu hv huv
  obtain ⟨b, hbu, hbv, rfl⟩ := eq_triple_of_mem hT₀G.1 hu₀ hv₀ huv
  -- ápice fresco
  set X : Finset V := {a, b} ∪ (nbrIn B u ∪ nbrIn B v ∪ nbrIn B a ∪ nbrIn B b) with hX
  have hXc : (X.card : ℝ) < α * Fintype.card V := by
    have hc : ∀ y, ((nbrIn B y).card : ℝ) ≤ d := fun y =>
      le_trans (by exact_mod_cast card_nbrIn_le B y) (hdeg y)
    have h1 : X.card ≤ 2 + ((nbrIn B u).card + (nbrIn B v).card + (nbrIn B a).card +
        (nbrIn B b).card) := by
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_le_two ?_)
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
      exact Finset.card_union_le _ _
    have h2 : (X.card : ℝ) ≤ 2 + (((nbrIn B u).card : ℝ) + (nbrIn B v).card +
        (nbrIn B a).card + (nbrIn B b).card) := by exact_mod_cast h1
    linarith [hc u, hc v, hc a, hc b]
  obtain ⟨t, hTt, htX⟩ := exists_fresh_apex hH3 hTG X hXc
  simp only [hX, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, nbrIn,
    Finset.mem_filter, Finset.mem_univ, true_and, not_or] at htX
  obtain ⟨⟨hta, htb⟩, ⟨⟨htu, htv⟩, hta'⟩, htb'⟩ := htX
  obtain ⟨-, hut, hvt⟩ := distinct_of_card_three hTt.1
  -- dos bisagras que evitan `B`
  obtain ⟨J₁, hJ₁, hJ₁B⟩ := exists_hinge_avoiding hH4 (Ne.symm hta) hTG hTt B d hdeg hta'
    hwin2
  have htb'' : s(t, b) ∉ B := by rwa [Sym2.eq_swap]
  obtain ⟨J₂, hJ₂, hJ₂B⟩ := exists_hinge_avoiding hH4 htb hTt hT₀G B d hdeg htb'' hwin2
  -- pertenencia de aristas a `H − B₀ − e`
  have hmem : ∀ f, f ∈ edges G → f ∉ B → f ≠ s(u, v) →
      f ∈ edges (subGraph G ((edges G \ B₀).erase s(u, v))) := fun f hf hfB hfe =>
    mem_edges_subGraph.2 ⟨Finset.mem_erase.2 ⟨hfe, Finset.mem_sdiff.2
      ⟨hf, fun h => hfB (hB₀ h)⟩⟩, hf⟩
  have huvT : ∀ c, s(u, v) ∈ triEdges ({u, v, c} : Finset V) := fun c =>
    mem_triEdges.2 ⟨by simp, by simp, huv⟩
  have hJsub : ∀ {c c' : V} {J : Finset (Sym2 V)}, IsHinge G lab F u v c c' J →
      Disjoint J B → J ⊆ edges (subGraph G ((edges G \ B₀).erase s(u, v))) := by
    intro c c' J hJ hJB f hf
    refine hmem f (hJ.1 hf) (Finset.disjoint_left.1 hJB hf) ?_
    rintro rfl
    exact Finset.disjoint_left.1 hJ.2.1 hf (Finset.mem_union_left _ (huvT c))
  have hWa : wedge u v a ⊆ edges (subGraph G ((edges G \ B₀).erase s(u, v))) := by
    intro f hf
    have hfT : f ∈ triEdges ({u, v, a} : Finset V) := by
      rw [triEdges_triple huv (Ne.symm hau) (Ne.symm hav)]
      exact Finset.mem_insert_of_mem hf
    have hfK := hTK hfT
    refine mem_edges_subGraph.2 ⟨Finset.mem_erase.2 ⟨?_, hfK⟩, triEdges_subset_edges hTG hfT⟩
    rintro rfl
    exact not_mem_wedge_uv huv (Ne.symm hau) (Ne.symm hav) hf
  have hWt : wedge u v t ⊆ edges (subGraph G ((edges G \ B₀).erase s(u, v))) := by
    intro f hf
    have hfT : f ∈ triEdges ({u, v, t} : Finset V) := by
      rw [triEdges_triple huv hut hvt]
      exact Finset.mem_insert_of_mem hf
    refine hmem f (triEdges_subset_edges hTt hfT) ?_ ?_
    · simp only [wedge, Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      exacts [htu, htv]
    · rintro rfl
      exact not_mem_wedge_uv huv hut hvt hf
  have hWb : wedge u v b ⊆ edges (subGraph G ((edges G \ B₀).erase s(u, v))) := by
    intro f hf
    have hfT : f ∈ triEdges ({u, v, b} : Finset V) := by
      rw [triEdges_triple huv (Ne.symm hbu) (Ne.symm hbv)]
      exact Finset.mem_insert_of_mem hf
    have hfK := (isAllowed_subGraph_iff.1 hT₀).2 hfT
    refine mem_edges_subGraph.2 ⟨Finset.mem_erase.2 ⟨?_, hfK⟩, triEdges_subset_edges hT₀G hfT⟩
    rintro rfl
    exact not_mem_wedge_uv huv (Ne.symm hbu) (Ne.symm hbv) hf
  have h1 := hinge_diff_mem hJ₁ huv (Ne.symm hau) (Ne.symm hav) hut hvt
    (hJsub hJ₁ hJ₁B) hWa hWt
  have h2 := hinge_diff_mem hJ₂ huv hut hvt (Ne.symm hbu) (Ne.symm hbv)
    (hJsub hJ₂ hJ₂B) hWt hWb
  have := Submodule.add_mem _ h1 h2
  rwa [sub_add_sub_cancel] at this

/-! ### Resultado principal -/

/-- **(1.1) con ventanas explícitas.** Bajo (H3), (H4), `Δ(B) ≤ d`, `2 + 4d < α n` y
`5 d 2^C(h,2) < α n`: `Λ_(H−B) = Λ_H ∩ {x : x|_B = 0}`. -/
theorem lattice_sdiff_eq_of_windows {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hH3 : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h)
    (B : Finset (Sym2 V)) (d : ℝ) (hdeg : ∀ x, (degIn B x : ℝ) ≤ d)
    (hwin1 : 2 + 4 * d < α * Fintype.card V)
    (hwin2 : 5 * d * 2 ^ h.choose 2 < α * Fintype.card V) :
    lattice (subGraph G (edges G \ B)) lab F = lattice G lab F ⊓ zeroOn B := by
  refine le_antisymm (lattice_sdiff_le G lab F B) (lattice_inf_zeroOn_le_of_pivots B ?_)
  intro B₀ hB₀ e _ _
  by_cases hex : ∃ T₀, IsAllowed (subGraph G (edges G \ B₀)) lab F T₀ ∧ e ∈ triEdges T₀
  · obtain ⟨T₀, hT₀, heT₀⟩ := hex
    exact ⟨T₀, fun T hT heT =>
      pivot_diff_mem hH3 hH4 B d hdeg hwin1 hwin2 hB₀ hT hT₀ heT heT₀⟩
  · exact ⟨∅, fun T hT heT => absurd ⟨T, hT, heT⟩ hex⟩

/-- **Teorema (S17, (1.1)): el retículo físico persiste bajo borrado disperso de aristas.**
Para `α > 0` y `h`, existen `η > 0` y `n₀` (dependientes sólo de `α` y `h`) tales que para
todo host `(G, lab)` de orden `n ≥ n₀` que cumple (H3) y (H4), y todo conjunto de aristas
`B` con `Δ(B) ≤ η n`,

    Λ_(H − B) = Λ_H ∩ {x : x_e = 0 para toda e ∈ B},

donde `H − B` es `subHost H ((edges H) \ B)`. Explícitamente `η = α / (8 · 2^C(h,2))` y
`n₀ = ⌈4/α⌉ + 1`. No se usan (H1), (H2), `C`, ni `B ⊆ E(H)`. -/
theorem sparse_edge_deletion_lattice (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ, ∀ (V I : Type) [Fintype V] (G : SimpleGraph V) (lab : V → I)
      (F : Set (Multiset I)), n₀ ≤ Fintype.card V →
      CommonNbrCond G lab F α →                 -- H3
      HingeCond G lab F α h →                   -- H4
      ∀ B : Finset (Sym2 V), (∀ x, (degIn B x : ℝ) ≤ η * Fintype.card V) →
        lattice (subGraph G (edges G \ B)) lab F = lattice G lab F ⊓ zeroOn B := by
  set M : ℝ := 2 ^ h.choose 2 with hM
  have hM1 : (1 : ℝ) ≤ M := one_le_pow₀ (by norm_num)
  refine ⟨α / (8 * M), by positivity, ⌈4 / α⌉₊ + 1, ?_⟩
  intro V I _ G lab F hn hH3 hH4 B hdeg
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hnα : 4 / α < n := by
    have h1 : (4 / α) ≤ ⌈4 / α⌉₊ := Nat.le_ceil _
    have h2 : ((⌈4 / α⌉₊ + 1 : ℕ) : ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hn
    push_cast at h2
    linarith
  have hαn : 4 < α * n := by
    have := (div_lt_iff₀' hα).1 hnα
    linarith
  have hn0 : 0 < n := lt_trans (by positivity) hnα
  refine lattice_sdiff_eq_of_windows hH3 hH4 B (α / (8 * M) * n) hdeg ?_ ?_
  · have : 4 * (α / (8 * M) * n) ≤ α * n / 2 := by
      rw [show 4 * (α / (8 * M) * n) = (α * n / 2) / M by field_simp; ring]
      exact div_le_self (by positivity) hM1
    linarith
  · have : 5 * (α / (8 * M) * n) * M = 5 / 8 * (α * n) := by field_simp
    rw [this]
    nlinarith

end TypedTriangle.SparseEdge
