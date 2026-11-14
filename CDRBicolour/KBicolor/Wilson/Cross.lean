/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Count.Wilson.Cross
public import CDRBicolour.KBicolor.Pattern.Main

/-!
# Wilson cross blocks for an arbitrary finite bicoloured Latin pattern

The slots of the pattern are an arbitrary finite type `A`, not one slot per colour.
`Setup` embeds `g` disjoint groups of `card A * t` points in the labelled host.
For every oriented block of an STS on the groups and every pair of slots, choose a
free Latin square of order `t`. Its triples are allowed and edge-disjoint, cover
exactly the edges between different groups, and determine the entire Latin family.
In particular, the residual host is independent of these free choices.

This generalizes the cross-block part of the three-colour Wilson construction.
It does not assume or assert a decomposition of the residual host.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle
open CDRBicolour.Absorption.Count.Wilson

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}

/-- A labelled embedding of the groups, together with the finite Latin pattern. -/
structure Setup (lab : Fin n → Fin k) (κ : A → Fin k) (g t : ℕ) where
  embed : (Fin g × A × Fin t) ↪ Fin n
  label : ∀ i P α, lab (embed (i, P, α)) = κ P
  tau : A → A → A
  row : ∀ P, Function.Injective (tau P)
  col : ∀ Q, Function.Injective (fun P => tau P Q)
  row_surj : ∀ P, Function.Surjective (tau P)
  col_surj : ∀ Q, Function.Surjective (fun P => tau P Q)
  allowed : ∀ P Q, ({κ P, κ Q, κ (tau P Q)} : Multiset (Fin k)) ∈ bicF k

def gv (h : Setup lab κ g t) (i : Fin g) (P : A) (α : Fin t) : Fin n := h.embed (i, P, α)

theorem gv_inj (h : Setup lab κ g t) {i j : Fin g} {P Q : A} {α β : Fin t}
    (he : gv h i P α = gv h j Q β) : i = j ∧ P = Q ∧ α = β := by
  have := h.embed.injective he
  simpa only [Prod.mk.injEq] using this


variable {S : Finset (Finset (Fin g))}

/-- Indices of the Latin squares: an oriented block and the classes of rows and columns. -/
abbrev Ix (A : Type*) (S : Finset (Finset (Fin g))) := {o // o ∈ OT S} × A × A

/-- A family of Latin squares of order `t`. -/
abbrev LFam (A : Type*) (S : Finset (Finset (Fin g))) (t : ℕ) :=
  Ix A S → {l : Fin t → Fin t → Fin t // _root_.STS.IsLatin l}

/-- A cell: an index and a row and column. -/
abbrev Cell (A : Type*) (S : Finset (Finset (Fin g))) (t : ℕ) := Ix A S × Fin t × Fin t

/-- Class at position `k` of a cell's block. -/
def colOf (h : Setup lab κ g t) (x : Cell A S t) (k : Fin 3) : A := ![x.1.2.1, x.1.2.2, h.tau x.1.2.1 x.1.2.2] k

/-- Index at position `k` of a cell's block. -/
def idxOf (Λ : LFam A S t) (x : Cell A S t) (k : Fin 3) : Fin t :=
  ![x.2.1, x.2.2, (Λ x.1).1 x.2.1 x.2.2] k

/-- Group at position `k`. -/
def grpOf (x : Cell A S t) (k : Fin 3) : Fin g := grp3 x.1.1.1 k

/-- The point at position `k`. -/
def pos (h : Setup lab κ g t) (Λ : LFam A S t) (x : Cell A S t) (k : Fin 3) : Fin n :=
  gv h (grpOf x k) (colOf h x k) (idxOf Λ x k)

/-- The block of a cell. -/
def blk (h : Setup lab κ g t) (Λ : LFam A S t) (x : Cell A S t) : Finset (Fin n) :=
  {pos h Λ x 0, pos h Λ x 1, pos h Λ x 2}

/-- **The cross blocks.** -/
def crossP (h : Setup lab κ g t) (Λ : LFam A S t) : Finset (Finset (Fin n)) :=
  univ.image (blk h Λ)

variable (h : Setup lab κ g t)

theorem ot_lt (x : Cell A S t) : x.1.1.1.1 < x.1.1.1.2.1 ∧ x.1.1.1.2.1 < x.1.1.1.2.2 :=
  ⟨(mem_OT.1 x.1.1.2).1, (mem_OT.1 x.1.1.2).2.1⟩

theorem grpOf_inj (x : Cell A S t) {k k' : Fin 3} (he : grpOf x k = grpOf x k') : k = k' :=
  grp3_inj (ot_lt x).1 (ot_lt x).2 he

theorem pos_ne (Λ : LFam A S t) (x : Cell A S t) {k k' : Fin 3} (hk : k ≠ k') :
    pos h Λ x k ≠ pos h Λ x k' := fun he => hk (grpOf_inj x (gv_inj h he).1)

theorem mem_blk {Λ : LFam A S t} {x : Cell A S t} {u : Fin n} :
    u ∈ blk h Λ x ↔ ∃ k, pos h Λ x k = u := by
  constructor
  · intro hu
    simp only [blk, mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp [blk]

theorem lab_pos (Λ : LFam A S t) (x : Cell A S t) (k : Fin 3) :
    lab (pos h Λ x k) = κ (colOf h x k) := h.label _ _ _

theorem blk_allowed (Λ : LFam A S t) (x : Cell A S t) :
    IsAllowed (kHost lab) (bicF k) (blk h Λ x) := by
  refine isAllowed_triple lab (pos_ne h Λ x (by decide)) (pos_ne h Λ x (by decide))
    (pos_ne h Λ x (by decide)) ?_
  rw [lab_pos h Λ x 0, lab_pos h Λ x 1, lab_pos h Λ x 2]
  exact h.allowed _ _

theorem crossP_allowed (Λ : LFam A S t) :
    ∀ T ∈ crossP h Λ, IsAllowed (kHost lab) (bicF k) T := by
  intro T hT
  obtain ⟨x, -, rfl⟩ := mem_image.1 hT
  exact blk_allowed h Λ x

/-- Two points shared by blocks of two cells, at different positions of the first: same oriented
block, same positions. -/
theorem share_two (hS : _root_.STS.IsSTS S) {Λ Λ' : LFam A S t} {x y : Cell A S t}
    {k k' l l' : Fin 3} (hk : k ≠ k') (h1 : pos h Λ x k = pos h Λ' y l)
    (h2 : pos h Λ x k' = pos h Λ' y l') : x.1.1 = y.1.1 ∧ k = l ∧ k' = l' := by
  have g1 := (gv_inj h h1).1
  have g2 := (gv_inj h h2).1
  have hne : grpOf x k ≠ grpOf x k' := fun e => hk (grpOf_inj x e)
  have hx : tri3 x.1.1.1 ∈ S := (mem_OT.1 x.1.1.2).2.2
  have hy : tri3 y.1.1.1 ∈ S := (mem_OT.1 y.1.1.2).2.2
  obtain ⟨B, -, hB⟩ := hS.2 _ _ hne
  have ex : tri3 x.1.1.1 = B :=
    hB _ ⟨hx, mem_tri3.2 ⟨k, rfl⟩, mem_tri3.2 ⟨k', rfl⟩⟩
  have ey : tri3 y.1.1.1 = B :=
    hB _ ⟨hy, mem_tri3.2 ⟨l, g1.symm⟩, mem_tri3.2 ⟨l', g2.symm⟩⟩
  have hxy : x.1.1.1 = y.1.1.1 :=
    tri3_inj (ot_lt x).1 (ot_lt x).2 (ot_lt y).1 (ot_lt y).2 (ex.trans ey.symm)
  have hxy' : x.1.1 = y.1.1 := Subtype.ext hxy
  refine ⟨hxy', ?_, ?_⟩
  · apply grpOf_inj x
    rw [g1]; simp only [grpOf, hxy]
  · apply grpOf_inj x
    rw [g2]; simp only [grpOf, hxy]

/-- Positions `0` and `1` determine the cell. -/
theorem cell_eq_01 {Λ Λ' : LFam A S t} {x y : Cell A S t} (ho : x.1.1 = y.1.1)
    (h0 : pos h Λ x 0 = pos h Λ' y 0) (h1 : pos h Λ x 1 = pos h Λ' y 1) : x = y := by
  obtain ⟨-, c0, i0⟩ := gv_inj h h0
  obtain ⟨-, c1, i1⟩ := gv_inj h h1
  obtain ⟨⟨o, P, Q⟩, α, β⟩ := x
  obtain ⟨⟨o', P', Q'⟩, α', β'⟩ := y
  simp only [colOf, idxOf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at c0 c1 i0 i1
  simp only at ho
  subst ho c0 c1 i0 i1
  rfl

/-- Any two positions determine the cell (same family). -/
theorem cell_eq_two {Λ : LFam A S t} {x y : Cell A S t} (ho : x.1.1 = y.1.1) {k k' : Fin 3}
    (hk : k ≠ k') (h1 : pos h Λ x k = pos h Λ y k) (h2 : pos h Λ x k' = pos h Λ y k') :
    x = y := by
  -- reduce to `k < k'`
  wlog hlt : k < k' generalizing k k'
  · exact this hk.symm h2 h1 (lt_of_le_of_ne (not_lt.1 hlt) hk.symm)
  obtain ⟨-, c1, i1⟩ := gv_inj h h1
  obtain ⟨-, c2, i2⟩ := gv_inj h h2
  obtain ⟨⟨o, P, Q⟩, α, β⟩ := x
  obtain ⟨⟨o', P', Q'⟩, α', β'⟩ := y
  simp only at ho
  subst ho
  fin_cases k <;> fin_cases k' <;> simp at hlt
  · -- `(0, 1)`
    simp only [colOf, idxOf, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at c1 c2 i1 i2
    subst c1 c2 i1 i2; rfl
  · -- `(0, 2)`
    simp only [colOf, idxOf, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at c1 c2 i1 i2
    subst c1 i1
    have hQ : Q = Q' := h.row P c2
    subst hQ
    have hβ : β = β' := ((Λ (o, P, Q)).2.1 α).1 i2
    subst hβ; rfl
  · -- `(1, 2)`
    simp only [colOf, idxOf, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at c1 c2 i1 i2
    subst c1 i1
    have hP : P = P' := h.col Q c2
    subst hP
    have hα : α = α' := ((Λ (o, P, Q)).2.2 β).1 i2
    subst hα; rfl

/-- **The cross blocks are edge-disjoint.** -/
theorem crossP_disj (hS : _root_.STS.IsSTS S) (Λ : LFam A S t) :
    ((crossP h Λ : Finset (Finset (Fin n))) : Set (Finset (Fin n))).PairwiseDisjoint
      triEdges := by
  intro X hX Y hY hne
  obtain ⟨x, -, rfl⟩ := mem_image.1 hX
  obtain ⟨y, -, rfl⟩ := mem_image.1 hY
  rw [Function.onFun, Finset.disjoint_left]
  intro e hex hey
  induction e using Sym2.ind with
  | _ u v =>
  obtain ⟨hux, hvx, huv⟩ := mem_tE.1 hex
  obtain ⟨huy, hvy, -⟩ := mem_tE.1 hey
  obtain ⟨k, rfl⟩ := (mem_blk h).1 hux
  obtain ⟨k', hk'⟩ := (mem_blk h).1 hvx
  obtain ⟨l, hl⟩ := (mem_blk h).1 huy
  obtain ⟨l', hl'⟩ := (mem_blk h).1 hvy
  have hkk : k ≠ k' := by rintro rfl; exact huv hk'
  obtain ⟨ho, rfl, rfl⟩ := share_two h hS hkk hl.symm (hk'.trans hl'.symm)
  exact hne (congrArg (blk h Λ) (cell_eq_two h ho hkk hl.symm (hk'.trans hl'.symm)))

/-- **Coverage**: two points of different groups lie in a common cross block. -/
theorem cover (hS : _root_.STS.IsSTS S) (Λ : LFam A S t) {p q : Fin g} (hpq : p ≠ q)
    (P Q : A) (α β : Fin t) :
    ∃ x : Cell A S t, gv h p P α ∈ blk h Λ x ∧ gv h q Q β ∈ blk h Λ x := by
  obtain ⟨B, ⟨hB, hpB, hqB⟩, -⟩ := hS.2 _ _ hpq
  obtain ⟨x0, y0, z0, h1, h2, h3, rfl⟩ := card_eq_three.1 (hS.1 B hB)
  obtain ⟨o, ho1, ho2, hoB⟩ := exists_sorted h1 h2 h3
  have hoS : o ∈ OT S := mem_OT.2 ⟨ho1, ho2, hoB ▸ hB⟩
  obtain ⟨k, hk⟩ := mem_tri3.1 (hoB ▸ hpB : p ∈ tri3 o)
  obtain ⟨k', hk'⟩ := mem_tri3.1 (hoB ▸ hqB : q ∈ tri3 o)
  have hkk : k ≠ k' := by rintro rfl; exact hpq (hk.symm.trans hk')
  -- a cell with prescribed point at positions `k` and `k'`
  suffices H : ∃ x : Cell A S t, x.1.1.1 = o ∧ colOf h x k = P ∧ idxOf Λ x k = α ∧
      colOf h x k' = Q ∧ idxOf Λ x k' = β by
    obtain ⟨x, hxo, c1, i1, c2, i2⟩ := H
    refine ⟨x, (mem_blk h).2 ⟨k, ?_⟩, (mem_blk h).2 ⟨k', ?_⟩⟩
    · simp only [pos, grpOf, hxo, hk, c1, i1]
    · simp only [pos, grpOf, hxo, hk', c2, i2]
  set ob : {o // o ∈ OT S} := ⟨o, hoS⟩
  fin_cases k <;> fin_cases k' <;> simp at hkk
  · exact ⟨((ob, P, Q), α, β), rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨Q', hQ'⟩ := h.row_surj P Q
    obtain ⟨β', hβ'⟩ := ((Λ (ob, P, Q')).2.1 α).2 β
    exact ⟨((ob, P, Q'), α, β'), rfl, rfl, rfl, hQ', hβ'⟩
  · exact ⟨((ob, Q, P), β, α), rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨P', hP'⟩ := h.col_surj P Q
    obtain ⟨α', hα'⟩ := ((Λ (ob, P', P)).2.2 α).2 β
    exact ⟨((ob, P', P), α', α), rfl, rfl, rfl, hP', hα'⟩
  · obtain ⟨Q', hQ'⟩ := h.row_surj Q P
    obtain ⟨β', hβ'⟩ := ((Λ (ob, Q, Q')).2.1 β).2 α
    exact ⟨((ob, Q, Q'), β, β'), rfl, hQ', hβ', rfl, rfl⟩
  · obtain ⟨P', hP'⟩ := h.col_surj Q P
    obtain ⟨α', hα'⟩ := ((Λ (ob, P', Q)).2.2 β).2 α
    exact ⟨((ob, P', Q), α', β), rfl, hP', hα', rfl, rfl⟩

/-- **The edges of the cross blocks** are exactly the pairs of points of different groups. -/
theorem mem_crossEdges (hS : _root_.STS.IsSTS S) (Λ : LFam A S t) {u v : Fin n} :
    s(u, v) ∈ (crossP h Λ).biUnion triEdges ↔
      ∃ p q P Q α β, p ≠ q ∧ u = gv h p P α ∧ v = gv h q Q β := by
  constructor
  · intro he
    obtain ⟨X, hX, he⟩ := mem_biUnion.1 he
    obtain ⟨x, -, rfl⟩ := mem_image.1 hX
    obtain ⟨hu, hv, huv⟩ := mem_tE.1 he
    obtain ⟨k, rfl⟩ := (mem_blk h).1 hu
    obtain ⟨k', rfl⟩ := (mem_blk h).1 hv
    have hkk : k ≠ k' := by rintro rfl; exact huv rfl
    exact ⟨grpOf x k, grpOf x k', colOf h x k, colOf h x k', idxOf Λ x k, idxOf Λ x k',
      fun e => hkk (grpOf_inj x e), rfl, rfl⟩
  · rintro ⟨p, q, P, Q, α, β, hpq, rfl, rfl⟩
    obtain ⟨x, hu, hv⟩ := cover h hS Λ hpq P Q α β
    refine mem_biUnion.2 ⟨blk h Λ x, mem_image.2 ⟨x, mem_univ _, rfl⟩, mem_tE.2 ⟨hu, hv, ?_⟩⟩
    intro e
    exact hpq (gv_inj h e).1

/-- **The cross blocks determine the Latin squares.** -/
theorem crossP_inj (hS : _root_.STS.IsSTS S) : Function.Injective (crossP (S := S) h) := by
  intro Λ Λ' he
  funext i
  apply Subtype.ext
  funext α β
  set x : Cell A S t := (i, α, β)
  have hx : blk h Λ x ∈ crossP h Λ' := by rw [← he]; exact mem_image.2 ⟨x, mem_univ _, rfl⟩
  obtain ⟨y, -, hy⟩ := mem_image.1 hx
  have m0 : pos h Λ x 0 ∈ blk h Λ' y := by rw [hy]; exact (mem_blk h).2 ⟨0, rfl⟩
  have m1 : pos h Λ x 1 ∈ blk h Λ' y := by rw [hy]; exact (mem_blk h).2 ⟨1, rfl⟩
  have m2 : pos h Λ x 2 ∈ blk h Λ' y := by rw [hy]; exact (mem_blk h).2 ⟨2, rfl⟩
  obtain ⟨l0, e0⟩ := (mem_blk h).1 m0
  obtain ⟨l1, e1⟩ := (mem_blk h).1 m1
  obtain ⟨l2, e2⟩ := (mem_blk h).1 m2
  obtain ⟨ho, rfl, rfl⟩ := share_two h hS (by decide : (0 : Fin 3) ≠ 1) e0.symm e1.symm
  have hxy : x = y := cell_eq_01 h ho e0.symm e1.symm
  obtain ⟨-, -, hl2⟩ := share_two h hS (by decide : (0 : Fin 3) ≠ 2) e0.symm e2.symm
  subst hl2
  have i2 := (gv_inj h e2).2.2
  rw [← hxy] at i2
  simpa [idxOf, x] using i2.symm


end CDRBicolour.KBicolor.Wilson
