/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Count.ProfileCount

/-!
# Optimal counting constant, part 1: the cross blocks (item 4)

`g` groups `G_0, …, G_{g−1}`, each with exactly `t` points of every class: the point of class `P`,
group `i`, index `α < t` is `gv i P α = cbase P + i t + α`.  The rest of each class is the
reserve `R`.

For an oriented block `(i, j, l)` (`i < j < l`) of a Steiner triple system on the group indices and
classes `P, Q`, a Latin square `Λ` of order `t` gives the blocks
`{gv i P α, gv j Q β, gv l (τ P Q) (Λ α β)}`, with

    τ = [[B, A, C], [A, C, B], [C, B, A]].

Every row and column of `τ` is a permutation, and `{P, Q, τ P Q}` always has exactly two classes,
so *any* Latin squares give strictly bicoloured blocks covering every pair between different groups
exactly once.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Count.Wilson

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

/-! ### The colour pattern -/

/-- `τ P Q`: the class of the symbols in the cells with row class `P` and column class `Q`. -/
def tau : Fin 3 → Fin 3 → Fin 3 := ![![1, 0, 2], ![0, 2, 1], ![2, 1, 0]]

theorem tau_row_inj (P : Fin 3) : Function.Injective (tau P) := by
  revert P; decide

theorem tau_col_inj (Q : Fin 3) : Function.Injective fun P => tau P Q := by
  revert Q; decide

theorem tau_row_surj (P R : Fin 3) : ∃ Q, tau P Q = R := by
  revert P R; decide

theorem tau_col_surj (Q R : Fin 3) : ∃ P, tau P Q = R := by
  revert Q R; decide

theorem tau_cdrF (P Q : Fin 3) : ({P, Q, tau P Q} : Multiset (Fin 3)) ∈ cdrF := by
  revert P Q; unfold cdrF; decide

/-! ### Group points -/

/-- Start of class `P`. -/
def cbase (a b : ℕ) (P : Fin 3) : ℕ := if P = 0 then 0 else if P = 1 then a else a + b

/-- Size of class `P`. -/
def csize (a b c : ℕ) (P : Fin 3) : ℕ := if P = 0 then a else if P = 1 then b else c

/-- Size conditions: `g` groups of `t` points per class fit. -/
structure WCond (a b c g t : ℕ) : Prop where
  hA : g * t ≤ a
  hB : g * t ≤ b
  hC : g * t ≤ c
  ht : 0 < t

variable {a b c g t : ℕ}

theorem gt_le_csize (h : WCond a b c g t) (P : Fin 3) : g * t ≤ csize a b c P := by
  unfold csize; split_ifs
  · exact h.hA
  · exact h.hB
  · exact h.hC

theorem cbase_add_csize (P : Fin 3) : cbase a b P + csize a b c P ≤ a + b + c := by
  unfold cbase csize; split_ifs <;> omega

theorem it_lt {i α : ℕ} (hi : i < g) (hα : α < t) : i * t + α < g * t := by
  have : (i + 1) * t ≤ g * t := Nat.mul_le_mul_right t hi
  rw [Nat.succ_mul] at this
  omega

/-- The point of class `P`, group `i`, index `α`. -/
def gv (h : WCond a b c g t) (i : Fin g) (P : Fin 3) (α : Fin t) : Fin (a + b + c) :=
  ⟨cbase a b P + (i.val * t + α.val), by
    have h1 := it_lt i.isLt α.isLt
    have h2 := gt_le_csize h P
    have h3 := cbase_add_csize (a := a) (b := b) (c := c) P
    omega⟩

theorem gv_val (h : WCond a b c g t) (i : Fin g) (P : Fin 3) (α : Fin t) :
    (gv h i P α).val = cbase a b P + (i.val * t + α.val) := rfl

theorem col3_gv (h : WCond a b c g t) (i : Fin g) (P : Fin 3) (α : Fin t) :
    col3 a b c (gv h i P α) = P := by
  have h1 := it_lt i.isLt α.isLt
  have hA := h.hA; have hB := h.hB; have hC := h.hC
  unfold col3
  rw [gv_val]
  fin_cases P <;> simp [cbase] <;> omega

theorem div_mod_it {i α : ℕ} (hα : α < t) : (i * t + α) / t = i ∧ (i * t + α) % t = α := by
  have ht : 0 < t := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ ht, Nat.div_eq_of_lt hα, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hα]

/-- Decoding a group point. -/
theorem gv_inj (h : WCond a b c g t) {i i' : Fin g} {P P' : Fin 3} {α α' : Fin t}
    (he : gv h i P α = gv h i' P' α') : i = i' ∧ P = P' ∧ α = α' := by
  have hP : P = P' := by
    have := congrArg (col3 a b c) he
    rwa [col3_gv, col3_gv] at this
  subst hP
  have hv := congrArg Fin.val he
  rw [gv_val, gv_val] at hv
  have e : i.val * t + α.val = i'.val * t + α'.val := by omega
  obtain ⟨d1, m1⟩ := div_mod_it (i := i.val) α.isLt
  obtain ⟨d2, m2⟩ := div_mod_it (i := i'.val) α'.isLt
  rw [e] at d1 m1
  exact ⟨Fin.ext (d1.symm.trans d2), rfl, Fin.ext (m1.symm.trans m2)⟩

/-- Group points are in the first `g t` points of their class. -/
theorem gv_lt (h : WCond a b c g t) (i : Fin g) (P : Fin 3) (α : Fin t) :
    (gv h i P α).val < cbase a b P + g * t := by
  rw [gv_val]; have := it_lt i.isLt α.isLt; omega

/-- A point among the first `g t` of its class is a group point. -/
theorem exists_gv (h : WCond a b c g t) (v : Fin (a + b + c))
    (hv : v.val < cbase a b (col3 a b c v) + g * t) :
    ∃ i α, v = gv h i (col3 a b c v) α := by
  have hlo : cbase a b (col3 a b c v) ≤ v.val := by
    unfold cbase col3; split_ifs <;> simp_all <;> omega
  set k := v.val - cbase a b (col3 a b c v) with hk
  have hkt : k < g * t := by omega
  have ht := h.ht
  have hi : k / t < g := by
    rw [Nat.div_lt_iff_lt_mul ht]; exact hkt
  refine ⟨⟨k / t, hi⟩, ⟨k % t, Nat.mod_lt _ ht⟩, Fin.ext ?_⟩
  rw [gv_val]
  simp only
  have := Nat.div_add_mod k t
  rw [Nat.mul_comm] at this
  omega

theorem mem_tE {V : Type*} [DecidableEq V] {T : Finset V} {u w : V} :
    s(u, w) ∈ triEdges T ↔ u ∈ T ∧ w ∈ T ∧ u ≠ w := by
  simp [triEdges, Sym2.mk_isDiag_iff, and_assoc]

/-! ### Oriented blocks of the design on the groups -/

section Design

variable (S : Finset (Finset (Fin g)))

/-- The point set of an ordered triple. -/
def tri3 (o : Fin g × Fin g × Fin g) : Finset (Fin g) := {o.1, o.2.1, o.2.2}

/-- Oriented blocks: increasing triples whose point set is a block. -/
def OT : Finset (Fin g × Fin g × Fin g) :=
  univ.filter fun o => o.1 < o.2.1 ∧ o.2.1 < o.2.2 ∧ tri3 o ∈ S

variable {S}

theorem mem_OT {o : Fin g × Fin g × Fin g} :
    o ∈ OT S ↔ o.1 < o.2.1 ∧ o.2.1 < o.2.2 ∧ tri3 o ∈ S := by
  simp [OT]

theorem tri3_inj {o o' : Fin g × Fin g × Fin g} (h1 : o.1 < o.2.1) (h2 : o.2.1 < o.2.2)
    (h1' : o'.1 < o'.2.1) (h2' : o'.2.1 < o'.2.2) (he : tri3 o = tri3 o') : o = o' := by
  have m : ∀ x, x ∈ tri3 o ↔ x ∈ tri3 o' := fun x => by rw [he]
  have a1 := (m o.1).1 (by simp [tri3])
  have a2 := (m o.2.1).1 (by simp [tri3])
  have a3 := (m o.2.2).1 (by simp [tri3])
  have b1 := (m o'.1).2 (by simp [tri3])
  have b2 := (m o'.2.1).2 (by simp [tri3])
  have b3 := (m o'.2.2).2 (by simp [tri3])
  simp only [tri3, mem_insert, mem_singleton, Fin.ext_iff] at a1 a2 a3 b1 b2 b3
  rw [Fin.lt_def] at h1 h2 h1' h2'
  obtain ⟨x, y, z⟩ := o
  obtain ⟨x', y', z'⟩ := o'
  simp only at *
  have e1 : x.val = x'.val := by omega
  have e2 : y.val = y'.val := by omega
  have e3 : z.val = z'.val := by omega
  rw [Fin.ext e1, Fin.ext e2, Fin.ext e3]

theorem exists_sorted {x y z : Fin g} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ o : Fin g × Fin g × Fin g, o.1 < o.2.1 ∧ o.2.1 < o.2.2 ∧ tri3 o = {x, y, z} := by
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  · exact ⟨(x, y, z), h1, h3, rfl⟩
  · exact ⟨(x, z, y), h2, h3, by ext; simp [tri3]; tauto⟩
  · exact absurd (h1.trans h3) (not_lt.2 h2.le)
  · exact ⟨(z, x, y), h2, h1, by ext; simp [tri3]; tauto⟩
  · exact ⟨(y, x, z), h1, h2, by ext; simp [tri3]; tauto⟩
  · exact absurd (h3.trans h1) (not_lt.2 h2.le)
  · exact ⟨(y, z, x), h3, h2, by ext; simp [tri3]; tauto⟩
  · exact ⟨(z, y, x), h3, h1, by ext; simp [tri3]; tauto⟩

/-- The `k`-th group of an oriented block. -/
def grp3 (o : Fin g × Fin g × Fin g) (k : Fin 3) : Fin g := ![o.1, o.2.1, o.2.2] k

theorem grp3_inj {o : Fin g × Fin g × Fin g} (h1 : o.1 < o.2.1) (h2 : o.2.1 < o.2.2)
    {k k' : Fin 3} (he : grp3 o k = grp3 o k') : k = k' := by
  rw [Fin.lt_def] at h1 h2
  fin_cases k <;> fin_cases k' <;> simp [grp3, Fin.ext_iff] at he ⊢ <;> omega

theorem mem_tri3 {o : Fin g × Fin g × Fin g} {p : Fin g} : p ∈ tri3 o ↔ ∃ k, grp3 o k = p := by
  constructor
  · intro h
    simp only [tri3, mem_insert, mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp [tri3, grp3]

end Design

/-! ### The cross blocks -/

section Cross

variable {S : Finset (Finset (Fin g))}

/-- Indices of the Latin squares: an oriented block and the classes of rows and columns. -/
abbrev Ix (S : Finset (Finset (Fin g))) := {o // o ∈ OT S} × Fin 3 × Fin 3

/-- A family of Latin squares of order `t`. -/
abbrev LFam (S : Finset (Finset (Fin g))) (t : ℕ) :=
  Ix S → {l : Fin t → Fin t → Fin t // _root_.STS.IsLatin l}

/-- A cell: an index and a row and column. -/
abbrev Cell (S : Finset (Finset (Fin g))) (t : ℕ) := Ix S × Fin t × Fin t

/-- Class at position `k` of a cell's block. -/
def colOf (x : Cell S t) (k : Fin 3) : Fin 3 := ![x.1.2.1, x.1.2.2, tau x.1.2.1 x.1.2.2] k

/-- Index at position `k` of a cell's block. -/
def idxOf (Λ : LFam S t) (x : Cell S t) (k : Fin 3) : Fin t :=
  ![x.2.1, x.2.2, (Λ x.1).1 x.2.1 x.2.2] k

/-- Group at position `k`. -/
def grpOf (x : Cell S t) (k : Fin 3) : Fin g := grp3 x.1.1.1 k

/-- The point at position `k`. -/
def pos (h : WCond a b c g t) (Λ : LFam S t) (x : Cell S t) (k : Fin 3) : Fin (a + b + c) :=
  gv h (grpOf x k) (colOf x k) (idxOf Λ x k)

/-- The block of a cell. -/
def blk (h : WCond a b c g t) (Λ : LFam S t) (x : Cell S t) : Finset (Fin (a + b + c)) :=
  {pos h Λ x 0, pos h Λ x 1, pos h Λ x 2}

/-- **The cross blocks.** -/
def crossP (h : WCond a b c g t) (Λ : LFam S t) : Finset (Finset (Fin (a + b + c))) :=
  univ.image (blk h Λ)

variable (h : WCond a b c g t)

theorem ot_lt (x : Cell S t) : x.1.1.1.1 < x.1.1.1.2.1 ∧ x.1.1.1.2.1 < x.1.1.1.2.2 :=
  ⟨(mem_OT.1 x.1.1.2).1, (mem_OT.1 x.1.1.2).2.1⟩

theorem grpOf_inj (x : Cell S t) {k k' : Fin 3} (he : grpOf x k = grpOf x k') : k = k' :=
  grp3_inj (ot_lt x).1 (ot_lt x).2 he

theorem pos_ne (Λ : LFam S t) (x : Cell S t) {k k' : Fin 3} (hk : k ≠ k') :
    pos h Λ x k ≠ pos h Λ x k' := fun he => hk (grpOf_inj x (gv_inj h he).1)

theorem mem_blk {Λ : LFam S t} {x : Cell S t} {u : Fin (a + b + c)} :
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

theorem col3_pos (Λ : LFam S t) (x : Cell S t) (k : Fin 3) :
    col3 a b c (pos h Λ x k) = colOf x k := col3_gv h _ _ _

theorem blk_allowed (Λ : LFam S t) (x : Cell S t) :
    IsAllowed (cdrHost a b c) cdrF (blk h Λ x) := by
  refine isAllowed_triple (col3 a b c) (pos_ne h Λ x (by decide)) (pos_ne h Λ x (by decide))
    (pos_ne h Λ x (by decide)) ?_
  rw [col3_pos, col3_pos, col3_pos]
  exact tau_cdrF _ _

theorem crossP_allowed (Λ : LFam S t) :
    ∀ T ∈ crossP h Λ, IsAllowed (cdrHost a b c) cdrF T := by
  intro T hT
  obtain ⟨x, -, rfl⟩ := mem_image.1 hT
  exact blk_allowed h Λ x

/-- Two points shared by blocks of two cells, at different positions of the first: same oriented
block, same positions. -/
theorem share_two (hS : _root_.STS.IsSTS S) {Λ Λ' : LFam S t} {x y : Cell S t}
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
theorem cell_eq_01 {Λ Λ' : LFam S t} {x y : Cell S t} (ho : x.1.1 = y.1.1)
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
theorem cell_eq_two {Λ : LFam S t} {x y : Cell S t} (ho : x.1.1 = y.1.1) {k k' : Fin 3}
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
    have hQ : Q = Q' := tau_row_inj P c2
    subst hQ
    have hβ : β = β' := ((Λ (o, P, Q)).2.1 α).1 i2
    subst hβ; rfl
  · -- `(1, 2)`
    simp only [colOf, idxOf, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at c1 c2 i1 i2
    subst c1 i1
    have hP : P = P' := tau_col_inj Q c2
    subst hP
    have hα : α = α' := ((Λ (o, P, Q)).2.2 β).1 i2
    subst hα; rfl

/-- **The cross blocks are edge-disjoint.** -/
theorem crossP_disj (hS : _root_.STS.IsSTS S) (Λ : LFam S t) :
    ((crossP h Λ : Finset (Finset (Fin (a + b + c)))) : Set (Finset (Fin (a + b + c)))).PairwiseDisjoint
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
theorem cover (hS : _root_.STS.IsSTS S) (Λ : LFam S t) {p q : Fin g} (hpq : p ≠ q)
    (P Q : Fin 3) (α β : Fin t) :
    ∃ x : Cell S t, gv h p P α ∈ blk h Λ x ∧ gv h q Q β ∈ blk h Λ x := by
  obtain ⟨B, ⟨hB, hpB, hqB⟩, -⟩ := hS.2 _ _ hpq
  obtain ⟨x0, y0, z0, h1, h2, h3, rfl⟩ := card_eq_three.1 (hS.1 B hB)
  obtain ⟨o, ho1, ho2, hoB⟩ := exists_sorted h1 h2 h3
  have hoS : o ∈ OT S := mem_OT.2 ⟨ho1, ho2, hoB ▸ hB⟩
  obtain ⟨k, hk⟩ := mem_tri3.1 (hoB ▸ hpB : p ∈ tri3 o)
  obtain ⟨k', hk'⟩ := mem_tri3.1 (hoB ▸ hqB : q ∈ tri3 o)
  have hkk : k ≠ k' := by rintro rfl; exact hpq (hk.symm.trans hk')
  -- a cell with prescribed point at positions `k` and `k'`
  suffices H : ∃ x : Cell S t, x.1.1.1 = o ∧ colOf x k = P ∧ idxOf Λ x k = α ∧
      colOf x k' = Q ∧ idxOf Λ x k' = β by
    obtain ⟨x, hxo, c1, i1, c2, i2⟩ := H
    refine ⟨x, (mem_blk h).2 ⟨k, ?_⟩, (mem_blk h).2 ⟨k', ?_⟩⟩
    · simp only [pos, grpOf, hxo, hk, c1, i1]
    · simp only [pos, grpOf, hxo, hk', c2, i2]
  set ob : {o // o ∈ OT S} := ⟨o, hoS⟩
  fin_cases k <;> fin_cases k' <;> simp at hkk
  · exact ⟨((ob, P, Q), α, β), rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨Q', hQ'⟩ := tau_row_surj P Q
    obtain ⟨β', hβ'⟩ := ((Λ (ob, P, Q')).2.1 α).2 β
    exact ⟨((ob, P, Q'), α, β'), rfl, rfl, rfl, hQ', hβ'⟩
  · exact ⟨((ob, Q, P), β, α), rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨P', hP'⟩ := tau_col_surj P Q
    obtain ⟨α', hα'⟩ := ((Λ (ob, P', P)).2.2 α).2 β
    exact ⟨((ob, P', P), α', α), rfl, rfl, rfl, hP', hα'⟩
  · obtain ⟨Q', hQ'⟩ := tau_row_surj Q P
    obtain ⟨β', hβ'⟩ := ((Λ (ob, Q, Q')).2.1 β).2 α
    exact ⟨((ob, Q, Q'), β, β'), rfl, hQ', hβ', rfl, rfl⟩
  · obtain ⟨P', hP'⟩ := tau_col_surj Q P
    obtain ⟨α', hα'⟩ := ((Λ (ob, P', Q)).2.2 β).2 α
    exact ⟨((ob, P', Q), α', β), rfl, hP', hα', rfl, rfl⟩

/-- **The edges of the cross blocks** are exactly the pairs of points of different groups. -/
theorem mem_crossEdges (hS : _root_.STS.IsSTS S) (Λ : LFam S t) {u v : Fin (a + b + c)} :
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
    exact ⟨grpOf x k, grpOf x k', colOf x k, colOf x k', idxOf Λ x k, idxOf Λ x k',
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
  set x : Cell S t := (i, α, β)
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

end Cross

end CDRBicolour.Absorption.Count.Wilson
