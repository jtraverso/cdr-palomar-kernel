/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-!
# Global finite macro-round bank, part 0: setting, degrees, cells and the supply interface (V40)

* Resource edges are `Sym2 V` for a finite vertex type `V`; an edge set is a `Finset (Sym2 V)`.
* `deg B v` is the used-edge degree of `v` in `B`; `satSet q B` is the set of vertices of degree
  at least `q` (the saturated set).
* `MacroSetting V Q C` carries the data: edge charges `w`, catalog charges `g`, the subgroup map
  `K`, the off/on basal predicate, the number of colors `P`, the saturation threshold `q`, the
  cell size bound `E` and the smallness threshold `zmax`.  `Bstar = 2 * card C * P`.
* `Cell V` is a pair of finite edge sets `A`, `Y`; its total is `A ∪ Y`.  The mode `off` is `A`,
  the mode `on` is `A ∪ Y`.
* `CellSupply S` is the **cell-supply interface** (an intermediate hypothesis, not the native G3
  theorem): for every used-edge set of maximum degree `≤ q + Bstar * E` and every `Z` with
  `card Z ≤ zmax`, every active label `(sign, c, color)` (`g c ∈ K Z`) has a good cell.
-/

@[expose] public section

namespace S07V40

open Finset Classical

noncomputable section

variable {V : Type*} [Fintype V]

/-- Used-edge degree of `v` in the edge set `B`. -/
def deg (B : Finset (Sym2 V)) (v : V) : ℕ := (B.filter (fun e => v ∈ e)).card

/-- Saturated vertices: used-edge degree at least `q`. -/
def satSet (q : ℕ) (B : Finset (Sym2 V)) : Finset V := univ.filter (fun v => q ≤ deg B v)

/-- The edge set `S` avoids every vertex of `Z`. -/
def Avoids (Z : Finset V) (S : Finset (Sym2 V)) : Prop := ∀ e ∈ S, ∀ v ∈ Z, v ∉ e

/-- Signed element: `true` is `+`, `false` is `-`. -/
def sgnQ {Q : Type*} [AddCommGroup Q] (b : Bool) (x : Q) : Q := if b then x else -x

/-- Edge-additive charge of an edge set. -/
def charge {Q : Type*} [AddCommGroup Q] (w : Sym2 V → Q) (S : Finset (Sym2 V)) : Q :=
  ∑ e ∈ S, w e

lemma mem_satSet {q : ℕ} {B : Finset (Sym2 V)} {v : V} : v ∈ satSet q B ↔ q ≤ deg B v := by
  simp [satSet]

omit [Fintype V] in
lemma deg_mono {B B' : Finset (Sym2 V)} (h : B ⊆ B') (v : V) : deg B v ≤ deg B' v :=
  card_le_card (filter_subset_filter _ h)

omit [Fintype V] in
lemma deg_union_le (B S : Finset (Sym2 V)) (v : V) : deg (B ∪ S) v ≤ deg B v + S.card := by
  unfold deg
  rw [filter_union]
  exact (card_union_le _ _).trans (Nat.add_le_add_left (card_filter_le _ _) _)

omit [Fintype V] in
lemma deg_union_of_avoids {Z : Finset V} {B S : Finset (Sym2 V)} (h : Avoids Z S) {v : V}
    (hv : v ∈ Z) : deg (B ∪ S) v = deg B v := by
  unfold deg
  rw [filter_union]
  have : S.filter (fun e => v ∈ e) = ∅ :=
    filter_eq_empty_iff.2 (fun e he hve => h e he v hv hve)
  simp [this]

/-- Handshake bound: the degree sum is at most twice the number of edges. -/
lemma sum_deg_le (B : Finset (Sym2 V)) : ∑ v, deg B v ≤ 2 * B.card := by
  unfold deg
  simp_rw [card_filter]
  rw [sum_comm]
  calc ∑ e ∈ B, ∑ v, (if v ∈ e then 1 else 0) ≤ ∑ _e ∈ B, 2 := by
        refine sum_le_sum (fun e _ => ?_)
        induction e using Sym2.ind with
        | h a b =>
          rw [← card_filter]
          calc (univ.filter fun v => v ∈ s(a, b)).card ≤ ({a, b} : Finset V).card :=
                card_le_card (fun v hv => by simpa using hv)
            _ ≤ 2 := card_le_two
    _ = 2 * B.card := by simp [mul_comm]

/-- `q * |sat_q(B)| ≤ 2 |B|`. -/
lemma mul_card_satSet_le (q : ℕ) (B : Finset (Sym2 V)) :
    q * (satSet q B).card ≤ 2 * B.card :=
  calc q * (satSet q B).card = ∑ _v ∈ satSet q B, q := by simp [mul_comm]
    _ ≤ ∑ v ∈ satSet q B, deg B v := sum_le_sum (fun v hv => mem_satSet.1 hv)
    _ ≤ ∑ v, deg B v := sum_le_sum_of_subset (subset_univ _)
    _ ≤ 2 * B.card := sum_deg_le B

lemma satSet_mono (q : ℕ) {B B' : Finset (Sym2 V)} (h : B ⊆ B') : satSet q B ⊆ satSet q B' :=
  fun v hv => mem_satSet.2 ((mem_satSet.1 hv).trans (deg_mono h v))

lemma satSet_empty {q : ℕ} (hq : 0 < q) : satSet q (∅ : Finset (Sym2 V)) = ∅ := by
  ext v; simp [mem_satSet, deg]; omega

/-- The data of the macro-round construction.  All numerical constants are fixed here, before
any used-edge set is chosen. -/
structure MacroSetting (V Q C : Type*) [AddCommGroup Q] where
  /-- edge charges; the charge of an edge set is the sum -/
  w : Sym2 V → Q
  /-- catalog charges -/
  g : C → Q
  /-- the subgroup `K(Z)` attached to a saturated set -/
  K : Finset V → AddSubgroup Q
  /-- the off/on basal predicate on edge sets -/
  basal : Finset (Sym2 V) → Prop
  /-- number of colors (activation stages) -/
  P : ℕ
  /-- saturation threshold -/
  q : ℕ
  /-- size bound of one cell -/
  E : ℕ
  /-- smallness threshold for saturated sets used by the supply -/
  zmax : ℕ

/-- Labels: sign, catalog entry, color. -/
abbrev Lab (C : Type*) (P : ℕ) := Bool × C × Fin P

variable {Q C : Type*} [AddCommGroup Q] [Fintype C]

/-- Full-round size bound `Bstar = 2 * card C * P`. -/
def MacroSetting.Bstar (S : MacroSetting V Q C) : ℕ := 2 * Fintype.card C * S.P

lemma card_lab (P : ℕ) : Fintype.card (Lab C P) = 2 * Fintype.card C * P := by
  simp [Lab, Fintype.card_prod]; ring

/-- A physical cell: two finite edge sets. -/
structure Cell (V : Type*) where
  /-- the off part -/
  A : Finset (Sym2 V)
  /-- the charged part -/
  Y : Finset (Sym2 V)

/-- Total edge set of a cell (= its `on` mode). -/
def Cell.tot (c : Cell V) : Finset (Sym2 V) := c.A ∪ c.Y

/-- A good cell for label `l`, current used-edge set `B` and saturated set `Z`. -/
def GoodCell (S : MacroSetting V Q C) (B : Finset (Sym2 V)) (Z : Finset V) (l : Lab C S.P)
    (c : Cell V) : Prop :=
  Disjoint c.A c.Y ∧ S.basal c.A ∧ S.basal c.tot ∧ Disjoint c.tot B ∧ Avoids Z c.tot ∧
    c.tot.card ≤ S.E ∧ charge S.w c.Y = sgnQ l.1 (S.g l.2.1)

omit [Fintype V] [Fintype C] in
lemma GoodCell.mono {S : MacroSetting V Q C} {B B' : Finset (Sym2 V)} {Z : Finset V}
    {l : Lab C S.P} {c : Cell V} (h : GoodCell S B' Z l c) (hB : B ⊆ B') : GoodCell S B Z l c :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.mono_right hB, h.2.2.2.2⟩

/-- **Cell-supply interface** (intermediate hypothesis, to be discharged from H3/H4 by the local
work; it is *not* the native G3 theorem). -/
def CellSupply (S : MacroSetting V Q C) : Prop :=
  ∀ (B : Finset (Sym2 V)) (Z : Finset V), (∀ v, deg B v ≤ S.q + S.Bstar * S.E) →
    Z.card ≤ S.zmax → ∀ l : Lab C S.P, S.g l.2.1 ∈ S.K Z → ∃ c, GoodCell S B Z l c

/-- The basal predicate holds for `∅` and is inherited under disjoint unions. -/
def BasalInherit (S : MacroSetting V Q C) : Prop :=
  S.basal ∅ ∧ ∀ X Y : Finset (Sym2 V), Disjoint X Y → S.basal X → S.basal Y → S.basal (X ∪ Y)

/-- Strict changes of `K` along any increasing chain of small sets are at most `L`. -/
def ChainBound (S : MacroSetting V Q C) (L : ℕ) : Prop :=
  ∀ (n : ℕ) (Z : ℕ → Finset V), Monotone Z → (∀ i ≤ n, (Z i).card ≤ S.zmax) →
    ((range n).filter (fun i => S.K (Z (i + 1)) ≠ S.K (Z i))).card ≤ L

/-- At each `Z`, the catalog entries lying in `K Z` generate `K Z`.  (Part of the setting; the
construction and its counting invariants do not use it.) -/
def CatalogGenerates (S : MacroSetting V Q C) : Prop :=
  ∀ Z : Finset V, AddSubgroup.closure {x | ∃ c, S.g c = x ∧ S.g c ∈ S.K Z} = S.K Z

end

end S07V40
