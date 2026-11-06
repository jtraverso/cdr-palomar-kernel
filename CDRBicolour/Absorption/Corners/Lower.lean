/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Corners.Residual
public import CDRBicolour.Extensions.BlockTypes

/-!
# The three parts together (item 3, corners)

The planted packing is `P = P₀ ∪ P₁ ∪ P₂`, where `Pₓ` consists of the blocks `XX(X+2)` built on
class `X` with apices in class `X + 2` (`exists_part`).  A vertex `u` of class `X` in position `z`
sees, in the leave, `dₓ + 2t` points of its class and of class `X + 2` (as a pair vertex of
`Pₓ`), and `2(qₓ + t)` points of class `X + 1` (as an apex of `P_{X+1}`), where `t = [z < rₓ]`
(`union_counts`).
-/

@[expose] public section

noncomputable section

open Classical

namespace CDRBicolour.Absorption.Corners

open Finset SimpleGraph TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Refined CDRBicolour.BlockTypes

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3}

/-- The facts of one part, as produced by `exists_part`. -/
def PartFacts (lab : V → Fin 3) (P : Finset (Finset V)) (X W : Fin 3) {sX sW : ℕ}
    (fX : ZMod sX ↪ V) (fW : ZMod sW ↪ V) (dX rX qW rW : ℕ) : Prop :=
  (∀ z, #(LN lab P (fX z) X) = dX + (if z.val < rX then 2 else 0)) ∧
  (∀ z, #(LN lab P (fX z) W) = dX + (if z.val < rX then 2 else 0)) ∧
  (∀ z, #(LN lab P (fW z) X) = 2 * (qW + if z.val < rW then 1 else 0)) ∧
  (∀ u Y, ¬ ((lab u = X ∧ Y = X) ∨ (lab u = X ∧ Y = W) ∨ (lab u = W ∧ Y = X)) →
    LN lab P u Y = ∅)

theorem card_LN3 (P₀ P₁ P₂ : Finset (Finset V)) (u : V) (Y : Fin 3) :
    #(LN lab (P₀ ∪ P₁ ∪ P₂) u Y) = #(LN lab P₀ u Y ∪ LN lab P₁ u Y ∪ LN lab P₂ u Y) := by
  rw [LN_union, LN_union]

/-- **Leave counts of the union of the three parts.** -/
theorem union_counts {a b c : ℕ} [NeZero a] [NeZero b] [NeZero c] (d q r : Fin 3 → ℕ)
    (P₀ P₁ P₂ : Finset (Finset V))
    (f₀ : ZMod a ↪ V) (f₁ : ZMod b ↪ V) (f₂ : ZMod c ↪ V)
    (s₀ : ∀ v, lab v = 0 → ∃ z, f₀ z = v) (s₁ : ∀ v, lab v = 1 → ∃ z, f₁ z = v)
    (s₂ : ∀ v, lab v = 2 → ∃ z, f₂ z = v)
    (h₀ : PartFacts lab P₀ 0 2 f₀ f₂ (d 0) (r 0) (q 2) (r 2))
    (h₁ : PartFacts lab P₁ 1 0 f₁ f₀ (d 1) (r 1) (q 0) (r 0))
    (h₂ : PartFacts lab P₂ 2 1 f₂ f₁ (d 2) (r 2) (q 1) (r 1)) (u : V) :
    ∃ t ≤ 1, #(LN lab (P₀ ∪ P₁ ∪ P₂) u (lab u)) = d (lab u) + 2 * t ∧
      #(LN lab (P₀ ∪ P₁ ∪ P₂) u (lab u + 1)) = 2 * (q (lab u) + t) ∧
      #(LN lab (P₀ ∪ P₁ ∪ P₂) u (lab u + 2)) = d (lab u) + 2 * t := by
  obtain ⟨a1, a2, a3, a4⟩ := h₀
  obtain ⟨b1, b2, b3, b4⟩ := h₁
  obtain ⟨c1, c2, c3, c4⟩ := h₂
  have e : ∀ {A B C : Finset V}, B = ∅ → C = ∅ → #(A ∪ B ∪ C) = #A := by
    intro A B C hB hC; rw [hB, hC, union_empty, union_empty]
  have e' : ∀ {A B C : Finset V}, A = ∅ → C = ∅ → #(A ∪ B ∪ C) = #B := by
    intro A B C hA hC; rw [hA, hC, empty_union, union_empty]
  have e'' : ∀ {A B C : Finset V}, A = ∅ → B = ∅ → #(A ∪ B ∪ C) = #C := by
    intro A B C hA hB; rw [hA, hB, empty_union, empty_union]
  rcases (show lab u = 0 ∨ lab u = 1 ∨ lab u = 2 by omega) with hu | hu | hu
  · obtain ⟨z, rfl⟩ := s₀ u hu
    refine ⟨if z.val < r 0 then 1 else 0, by split_ifs <;> omega, ?_, ?_, ?_⟩
    · rw [card_LN3, hu, e (b4 _ _ (by rw [hu]; decide)) (c4 _ _ (by rw [hu]; decide)), a1]
      split_ifs <;> rfl
    · rw [card_LN3, hu, e' (a4 _ _ (by rw [hu]; decide)) (c4 _ _ (by rw [hu]; decide))]
      exact b3 z
    · rw [card_LN3, hu, show (0 : Fin 3) + 2 = 2 from rfl,
        e (b4 _ _ (by rw [hu]; decide)) (c4 _ _ (by rw [hu]; decide)), a2]
      split_ifs <;> rfl
  · obtain ⟨z, rfl⟩ := s₁ u hu
    refine ⟨if z.val < r 1 then 1 else 0, by split_ifs <;> omega, ?_, ?_, ?_⟩
    · rw [card_LN3, hu, e' (a4 _ _ (by rw [hu]; decide)) (c4 _ _ (by rw [hu]; decide)), b1]
      split_ifs <;> rfl
    · rw [card_LN3, hu, e'' (a4 _ _ (by rw [hu]; decide)) (b4 _ _ (by rw [hu]; decide))]
      exact c3 z
    · rw [card_LN3, hu, show (1 : Fin 3) + 2 = 0 from rfl,
        e' (a4 _ _ (by rw [hu]; decide)) (c4 _ _ (by rw [hu]; decide)), b2]
      split_ifs <;> rfl
  · obtain ⟨z, rfl⟩ := s₂ u hu
    refine ⟨if z.val < r 2 then 1 else 0, by split_ifs <;> omega, ?_, ?_, ?_⟩
    · rw [card_LN3, hu, e'' (a4 _ _ (by rw [hu]; decide)) (b4 _ _ (by rw [hu]; decide)), c1]
      split_ifs <;> rfl
    · rw [card_LN3, hu, e (b4 _ _ (by rw [hu]; decide)) (c4 _ _ (by rw [hu]; decide))]
      exact a3 z
    · rw [card_LN3, hu, show (2 : Fin 3) + 2 = 1 from rfl,
        e'' (a4 _ _ (by rw [hu]; decide)) (b4 _ _ (by rw [hu]; decide)), c2]
      split_ifs <;> rfl

/-- The leave degree is the sum of the three label counts. -/
theorem degL_eq (P : Finset (Finset V)) (u : V) :
    degL (P.biUnion triEdges) u = #(LN lab P u 0) + #(LN lab P u 1) + #(LN lab P u 2) := by
  have h : nbL (P.biUnion triEdges) u = LN lab P u 0 ∪ LN lab P u 1 ∪ LN lab P u 2 := by
    ext w
    simp only [nbL, LN, mem_filter, mem_univ, true_and, mem_union]
    rw [Sym2.eq_swap]
    constructor
    · intro hw
      rcases (show lab w = 0 ∨ lab w = 1 ∨ lab w = 2 by omega) with h | h | h
      · exact Or.inl (Or.inl ⟨h, hw⟩)
      · exact Or.inl (Or.inr ⟨h, hw⟩)
      · exact Or.inr ⟨h, hw⟩
    · rintro ((⟨-, hw⟩ | ⟨-, hw⟩) | ⟨-, hw⟩) <;> exact hw
  unfold degL
  rw [h, card_union_of_disjoint, card_union_of_disjoint]
  · rw [Finset.disjoint_left]; intro v h1 h2
    simp only [LN, mem_filter] at h1 h2; rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
  · rw [Finset.disjoint_left]; intro v h1 h2
    simp only [LN, mem_union, mem_filter] at h1 h2
    rcases h1 with h1 | h1 <;> rw [h1.2.1] at h2 <;> exact absurd h2.2.1 (by decide)

/-! ### Label bookkeeping -/

/-- In an admissible profile exactly one class is odd. -/
theorem adm_parity {a b c : ℕ} (h : AdmissibleProfile a b c) : a % 2 + b % 2 + c % 2 = 1 := by
  obtain ⟨e1, e2, e3⟩ := adm_even_mul h
  have hn := h.2.2.2.1
  rw [Nat.even_mul] at e1 e2 e3
  simp only [Nat.even_iff] at e1 e2 e3
  omega

theorem cnt_triple {W' : Type*} [DecidableEq W'] (col : W' → Fin 3) {u u' w : W'} (h1 : u ≠ u')
    (h2 : u ≠ w) (h3 : u' ≠ w) (j : Fin 3) :
    cnt col j {u, u', w} =
      (if col u = j then 1 else 0) + (if col u' = j then 1 else 0) + (if col w = j then 1 else 0) := by
  unfold cnt
  rw [filter_insert, filter_insert, filter_singleton]
  split_ifs <;> simp_all

/-- Edges of a block of type `XX(X+2)` have label pairs `XX` or `X(X+2)`. -/
theorem edge_labels {W' : Type*} [DecidableEq W'] {col : W' → Fin 3} {X : Fin 3} {u u' w p q : W'}
    (hu : col u = X) (hu' : col u' = X) (hw : col w = X + 2)
    (h : s(p, q) ∈ triEdges ({u, u', w} : Finset W')) :
    (col p = X ∧ col q = X) ∨ (col p = X ∧ col q = X + 2) ∨ (col p = X + 2 ∧ col q = X) := by
  simp only [triEdges, mem_filter, Finset.mk_mem_sym2_iff, mem_insert, mem_singleton,
    Sym2.mk_isDiag_iff] at h
  obtain ⟨⟨hp, hq⟩, hpq⟩ := h
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> simp_all

theorem labels_cross {X Y : Fin 3} (hXY : X ≠ Y) {lp lq : Fin 3}
    (h1 : (lp = X ∧ lq = X) ∨ (lp = X ∧ lq = X + 2) ∨ (lp = X + 2 ∧ lq = X))
    (h2 : (lp = Y ∧ lq = Y) ∨ (lp = Y ∧ lq = Y + 2) ∨ (lp = Y + 2 ∧ lq = Y)) : False := by
  revert h1 h2 hXY; revert X Y lp lq; decide

/-- Blocks of different parts are edge-disjoint. -/
theorem cross_disjoint {W' : Type*} [DecidableEq W'] {col : W' → Fin 3} {X Y : Fin 3} (hXY : X ≠ Y)
    {T T' : Finset W'}
    (hT : ∃ u u' w, T = {u, u', w} ∧ u ≠ u' ∧ col u = X ∧ col u' = X ∧ col w = X + 2)
    (hT' : ∃ u u' w, T' = {u, u', w} ∧ u ≠ u' ∧ col u = Y ∧ col u' = Y ∧ col w = Y + 2) :
    Disjoint (triEdges T) (triEdges T') := by
  obtain ⟨u, u', w, rfl, -, hu, hu', hw⟩ := hT
  obtain ⟨v, v', x, rfl, -, hv, hv', hx⟩ := hT'
  rw [Finset.disjoint_left]
  intro f h1 h2
  induction f using Sym2.ind with
  | _ p q =>
  exact labels_cross hXY (edge_labels hu hu' hw h1) (edge_labels hv hv' hx h2)

/-! ### The planted packing of the lower corner -/

/-- The class sizes. -/
abbrev sz (a b c : ℕ) (X : Fin 3) : ℕ := ![a, b, c] X

theorem shape_cnt {a b c : ℕ} {X : Fin 3} {T : Finset (Fin (a + b + c))}
    (hT : ∃ u u' w, T = {u, u', w} ∧ u ≠ u' ∧ col3 a b c u = X ∧ col3 a b c u' = X ∧
      col3 a b c w = X + 2) (j : Fin 3) :
    cnt (col3 a b c) j T = (if X = j then 2 else 0) + (if X + 2 = j then 1 else 0) := by
  obtain ⟨u, u', w, rfl, h1, hu, hu', hw⟩ := hT
  have h2 : u ≠ w := fun e => fin3_add2_ne X (by rw [← hw, ← e, hu])
  have h3 : u' ≠ w := fun e => fin3_add2_ne X (by rw [← hw, ← e, hu'])
  rw [cnt_triple _ h1 h2 h3, hu, hu', hw]
  split_ifs <;> simp_all

set_option maxHeartbeats 1600000 in
/-- **The planted minority packing of the lower corner.** -/
theorem lower_packing {a b c : ℕ} (h : AdmissibleProfile a b c) (d q r : Fin 3 → ℕ)
    (hr : ∀ X, r X < sz a b c X)
    (hdq : ∀ X, (d X : ℤ) = sz a b c X - 1 - sz a b c (X + 1) + 2 * q X)
    (hE : ∀ X, sz a b c X * d X + 2 * r X = 2 * (sz a b c (X + 2) * q (X + 2) + r (X + 2)))
    (hex : ∀ X, ¬ (d X = 0 ∧ (r X = 1 ∨ r X = 2)))
    (hsmall : ∀ X, 4 * d X + 64 ≤ sz a b c X ∧ d X + 3 ≤ sz a b c (X + 2)) :
    ∃ P : Finset (Finset (Fin (a + b + c))),
      (∀ T ∈ P, ∃ X : Fin 3, ∃ u u' w, T = {u, u', w} ∧ u ≠ u' ∧ col3 a b c u = X ∧
        col3 a b c u' = X ∧ col3 a b c w = X + 2) ∧
      (P : Set (Finset (Fin (a + b + c)))).PairwiseDisjoint triEdges ∧
      (∀ u, ∃ t ≤ 1, #(LN (col3 a b c) P u (col3 a b c u)) = d (col3 a b c u) + 2 * t ∧
        #(LN (col3 a b c) P u (col3 a b c u + 1)) = 2 * (q (col3 a b c u) + t) ∧
        #(LN (col3 a b c) P u (col3 a b c u + 2)) = d (col3 a b c u) + 2 * t) ∧
      #(P.filter fun T => cnt (col3 a b c) 0 T = 2 ∧ cnt (col3 a b c) 2 T = 1) =
        c * q 2 + r 2 := by
  have : NeZero a := ⟨h.1.ne'⟩
  have : NeZero b := ⟨h.2.1.ne'⟩
  have : NeZero c := ⟨h.2.2.1.ne'⟩
  have hp := adm_parity h
  have ca : csz (col3 a b c) 0 = a := by rw [csz_col3]; rfl
  have cb : csz (col3 a b c) 1 = b := by rw [csz_col3]; rfl
  have cc : csz (col3 a b c) 2 = c := by rw [csz_col3]; rfl
  obtain ⟨f₀, l₀, s₀⟩ := exists_cls_emb (col3 a b c) 0 ca
  obtain ⟨f₁, l₁, s₁⟩ := exists_cls_emb (col3 a b c) 1 cb
  obtain ⟨f₂, l₂, s₂⟩ := exists_cls_emb (col3 a b c) 2 cc
  have hd0 := hdq 0; have hd1 := hdq 1; have hd2 := hdq 2
  simp only [sz] at hd0 hd1 hd2
  norm_num at hd0 hd1 hd2
  have e0 := hE 0; have e1 := hE 1; have e2 := hE 2
  have r0 := hr 0; have r1 := hr 1; have r2 := hr 2
  have m0 := hsmall 0; have m1 := hsmall 1; have m2 := hsmall 2
  simp only [sz] at e0 e1 e2 r0 r1 r2 m0 m1 m2
  norm_num at e0 e1 e2 r0 r1 r2 m0 m1 m2
  obtain ⟨P₀, sh₀, dj₀, cd₀, a1, a2, a3, a4⟩ := exists_part (col3 a b c) (X := 0) (W := 2)
    (by decide) f₀ l₀ f₂ l₂ m0.1 r0 (fun hd => by omega) (hex 0) m0.2 r2 e0
  obtain ⟨P₁, sh₁, dj₁, -, b1, b2, b3, b4⟩ := exists_part (col3 a b c) (X := 1) (W := 0)
    (by decide) f₁ l₁ f₀ l₀ m1.1 r1 (fun hd => by omega) (hex 1) m1.2 r0 e1
  obtain ⟨P₂, sh₂, dj₂, -, c1, c2, c3, c4⟩ := exists_part (col3 a b c) (X := 2) (W := 1)
    (by decide) f₂ l₂ f₁ l₁ m2.1 r2 (fun hd => by omega) (hex 2) m2.2 r1 e2
  refine ⟨P₀ ∪ P₁ ∪ P₂, ?_, ?_, ?_, ?_⟩
  · intro T hT
    rcases mem_union.1 hT with hT | hT
    · rcases mem_union.1 hT with hT | hT
      · exact ⟨0, sh₀ T hT⟩
      · exact ⟨1, sh₁ T hT⟩
    · exact ⟨2, sh₂ T hT⟩
  · rw [coe_union, coe_union, Set.pairwiseDisjoint_union, Set.pairwiseDisjoint_union]
    refine ⟨⟨dj₀, dj₁, fun T hT T' hT' _ => cross_disjoint (by decide) (sh₀ T hT) (sh₁ T' hT')⟩,
      dj₂, fun T hT T' hT' _ => ?_⟩
    rcases hT with hT | hT
    · exact cross_disjoint (by decide) (sh₀ T hT) (sh₂ T' hT')
    · exact cross_disjoint (by decide) (sh₁ T hT) (sh₂ T' hT')
  · exact union_counts d q r P₀ P₁ P₂ f₀ f₁ f₂ s₀ s₁ s₂ ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
      ⟨c1, c2, c3, c4⟩
  · rw [filter_union, filter_union]
    have k0 : P₀.filter (fun T => cnt (col3 a b c) 0 T = 2 ∧ cnt (col3 a b c) 2 T = 1) = P₀ := by
      refine filter_true_of_mem fun T hT => ?_
      rw [shape_cnt (sh₀ T hT), shape_cnt (sh₀ T hT)]; decide
    have k1 : P₁.filter (fun T => cnt (col3 a b c) 0 T = 2 ∧ cnt (col3 a b c) 2 T = 1) = ∅ := by
      refine filter_false_of_mem fun T hT => ?_
      rw [shape_cnt (sh₁ T hT), shape_cnt (sh₁ T hT)]; decide
    have k2 : P₂.filter (fun T => cnt (col3 a b c) 0 T = 2 ∧ cnt (col3 a b c) 2 T = 1) = ∅ := by
      refine filter_false_of_mem fun T hT => ?_
      rw [shape_cnt (sh₂ T hT), shape_cnt (sh₂ T hT)]; decide
    rw [k0, k1, k2, union_empty, union_empty, cd₀]

end CDRBicolour.Absorption.Corners
