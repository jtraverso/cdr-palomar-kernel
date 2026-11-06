/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V36.NativeDegree
@[expose] public section

/-!
# V36 — the V35 gauge lemma instantiated on the native matrix of an original host

Rows `NRow G lab F` (active bipartite link components), columns `NCol G lab F` (all host edges
lying in an allowed triangle; every column is retained, including anchor columns and zero
columns), matrix `natB G lab F`. Only hypotheses: `0 < α` and the ORIGINAL H3
`CommonNbrCond G lab F α`.

* `nativeN α = n ⌊1/(2α)⌋₊`, `nativeM α = max 1 ⌈2 α n⌉₊` (`n = card V`).
* `native_card_le` — `card NRow ≤ nativeN α`.
* `native_hdeg` — every unanchored native row has `≥ nativeM α` distinct link-graph neighbours.
  (When `n ≥ 1`, `nativeM α = ⌈2 α n⌉₊`; the `max 1` only matters when `V` is empty, where
  there are no rows at all.)
* `native_gauge_bound` — V35 `gauge_bound` on `natB`: same data, `|t' i| ≤ (6 ⌊N/m⌋ + 1) L`.
* `native_const_le` — `6 ⌊N/m⌋ + 1 ≤ 3/(2α²) + 1` for every `n ≥ 1`.
* `native_gauge_alpha` — same data, `|t' i| ≤ (3/(2α²) + 1) L`, a constant depending only on
  `α`, valid for every host size (including `n = 0`, treated separately).
* `native_gauge_eighth`, `native_gauge_eighth_alpha` — quarter-integer data ⇒ eighth-integer
  `t'`, same bounds.
-/

open Finset Classical

noncomputable section

namespace S07V36

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.ActiveCover

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

variable (V) in
/-- The explicit row bound `N = n ⌊1/(2α)⌋₊`. -/
def nativeN (α : ℝ) : ℕ := Fintype.card V * ⌊1 / (2 * α)⌋₊

variable (V) in
/-- The explicit degree bound `m = max 1 ⌈2 α n⌉₊`. -/
def nativeM (α : ℝ) : ℕ := max 1 ⌈2 * α * Fintype.card V⌉₊

theorem native_card_le {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α) :
    Fintype.card (NRow G lab F) ≤ nativeN V α :=
  card_nrow_le hα hH3

theorem one_le_nativeM (α : ℝ) : 1 ≤ nativeM V α := le_max_left _ _

/-- **Native minimum degree** (from H3): every unanchored native row has at least
`nativeM α` distinct neighbours in the V35 link graph of `natB`. -/
theorem native_hdeg {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (i : NRow G lab F) (hi : ¬ S07V35.Anchored (natB G lab F) i) :
    nativeM V α ≤ (S07V35.nbrs (S07V35.linkGraph (natB G lab F)) i).card := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.2 ⟨i.1.1⟩
  have hpos : 0 < ⌈2 * α * Fintype.card V⌉₊ := Nat.ceil_pos.2 (by positivity)
  have hK : ⌈2 * α * Fintype.card V⌉₊ ≤ i.1.2.card := Nat.ceil_le.2 (comp_card_ge hH3 i.2)
  have hle := card_comp_le_nbrs i hi
  unfold nativeM
  rw [max_eq_right hpos]
  exact hK.trans hle

/-- **V35 gauge lemma on the native matrix.** For every `t : NRow → ℝ` whose data `natBᵀ t`
are bounded by `L ≥ 0` on every native column, some `t'` has exactly the same data on every
column and `|t' i| ≤ (6 ⌊N/m⌋ + 1) L` with `N = nativeN α`, `m = nativeM α`. -/
theorem native_gauge_bound {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (t : NRow G lab F → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : ∀ e, |S07V35.dat (natB G lab F) t e| ≤ L) :
    ∃ t' : NRow G lab F → ℝ, (∀ e, S07V35.dat (natB G lab F) t' e =
        S07V35.dat (natB G lab F) t e) ∧
      ∀ i, |t' i| ≤ ((6 * (nativeN V α / nativeM V α) + 1 : ℕ) : ℝ) * L :=
  S07V35.gauge_bound natB_linkMatrix (one_le_nativeM α) (native_card_le hα hH3)
    (native_hdeg hα hH3) t L hL hd

/-- **The constant depends only on `α`**: `6 ⌊N/m⌋ + 1 ≤ 3/(2α²) + 1` whenever `n ≥ 1`. -/
theorem native_const_le {α : ℝ} (hα : 0 < α) (hn : 0 < Fintype.card V) :
    ((6 * (nativeN V α / nativeM V α) + 1 : ℕ) : ℝ) ≤ 3 / (2 * α ^ 2) + 1 := by
  set q := nativeN V α / nativeM V α
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hqm : (q : ℝ) * nativeM V α ≤ nativeN V α := by
    exact_mod_cast Nat.div_mul_le_self _ _
  have hf : (⌊1 / (2 * α)⌋₊ : ℝ) ≤ 1 / (2 * α) := Nat.floor_le (by positivity)
  have hM : 2 * α * Fintype.card V ≤ (nativeM V α : ℝ) := by
    unfold nativeM
    push_cast
    exact (Nat.le_ceil _).trans (le_max_right _ _)
  have hN : (nativeN V α : ℝ) = Fintype.card V * ⌊1 / (2 * α)⌋₊ := by
    unfold nativeN; push_cast; ring
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have key : (q : ℝ) * (2 * α) * Fintype.card V ≤ 1 / (2 * α) * Fintype.card V := by
    calc (q : ℝ) * (2 * α) * Fintype.card V = q * (2 * α * Fintype.card V) := by ring
      _ ≤ q * nativeM V α := mul_le_mul_of_nonneg_left hM hq0
      _ ≤ nativeN V α := hqm
      _ = Fintype.card V * ⌊1 / (2 * α)⌋₊ := hN
      _ ≤ Fintype.card V * (1 / (2 * α)) := mul_le_mul_of_nonneg_left hf hnR.le
      _ = 1 / (2 * α) * Fintype.card V := by ring
  have h1 : (q : ℝ) * (2 * α) ≤ 1 / (2 * α) := le_of_mul_le_mul_right key hnR
  have h2 : (q : ℝ) ≤ 1 / (4 * α ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have : (q : ℝ) * (2 * α) * (2 * α) ≤ 1 / (2 * α) * (2 * α) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at this
    nlinarith
  have h3 : 6 * (1 / (4 * α ^ 2)) = 3 / (2 * α ^ 2) := by field_simp; ring
  push_cast
  linarith

/-- **Native gauge with an `α`-only constant.** Under the original H3 with `α > 0`, for every
`t` with native data bounded by `L ≥ 0`, some `t'` has the same data on every native column and
`|t' i| ≤ (3/(2α²) + 1) L` for every native row. -/
theorem native_gauge_alpha {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (t : NRow G lab F → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : ∀ e, |S07V35.dat (natB G lab F) t e| ≤ L) :
    ∃ t' : NRow G lab F → ℝ, (∀ e, S07V35.dat (natB G lab F) t' e =
        S07V35.dat (natB G lab F) t e) ∧
      ∀ i, |t' i| ≤ (3 / (2 * α ^ 2) + 1) * L := by
  obtain ⟨t', h1, h2⟩ := native_gauge_bound hα hH3 t L hL hd
  refine ⟨t', h1, fun i => (h2 i).trans (mul_le_mul_of_nonneg_right ?_ hL)⟩
  exact native_const_le hα (Fintype.card_pos_iff.2 ⟨i.1.1⟩)

/-- **Eighth-integer native gauge.** Quarter-integer data ⇒ eighth-integer `t'`, same data,
`|t' i| ≤ (6 ⌊N/m⌋ + 1) L`. -/
theorem native_gauge_eighth {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (t : NRow G lab F → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : ∀ e, |S07V35.dat (natB G lab F) t e| ≤ L)
    (hq : ∀ e, ∃ n : ℤ, S07V35.dat (natB G lab F) t e = n / 4) :
    ∃ t' : NRow G lab F → ℝ, (∀ e, S07V35.dat (natB G lab F) t' e =
        S07V35.dat (natB G lab F) t e) ∧
      (∀ i, |t' i| ≤ ((6 * (nativeN V α / nativeM V α) + 1 : ℕ) : ℝ) * L) ∧
      ∀ i, ∃ n : ℤ, t' i = n / 8 :=
  S07V35.gauge_bound_eighth natB_linkMatrix (one_le_nativeM α) (native_card_le hα hH3)
    (native_hdeg hα hH3) t L hL hd hq

/-- Eighth-integer native gauge with the `α`-only constant `3/(2α²) + 1`. -/
theorem native_gauge_eighth_alpha {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (t : NRow G lab F → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : ∀ e, |S07V35.dat (natB G lab F) t e| ≤ L)
    (hq : ∀ e, ∃ n : ℤ, S07V35.dat (natB G lab F) t e = n / 4) :
    ∃ t' : NRow G lab F → ℝ, (∀ e, S07V35.dat (natB G lab F) t' e =
        S07V35.dat (natB G lab F) t e) ∧
      (∀ i, |t' i| ≤ (3 / (2 * α ^ 2) + 1) * L) ∧ ∀ i, ∃ n : ℤ, t' i = n / 8 := by
  obtain ⟨t', h1, h2, h3⟩ := native_gauge_eighth hα hH3 t L hL hd hq
  refine ⟨t', h1, fun i => (h2 i).trans (mul_le_mul_of_nonneg_right ?_ hL), h3⟩
  exact native_const_le hα (Fintype.card_pos_iff.2 ⟨i.1.1⟩)

end S07V36
