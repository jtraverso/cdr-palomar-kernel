/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Pattern.Split
public import CDRBicolour.KBicolor.Pattern.Spread

/-!
# Hilton's amalgamation theorem for an arbitrary class type and support

Rows, columns and symbols are finite types `α, β, γ` with class maps `ρ, κ, τ : · → K` into a finite
type `K` of classes, and `ok : K → K → K → Prop` is a set of permitted class triples. An *outline*
is `M : K → K → K → ℕ` (row class, column class, symbol class) with the three marginal conditions of
an amalgamated Latin square and `M r c s = 0` whenever `¬ ok r c s`. We build a Latin square
`L : α → β → γ` with `ok (ρ x) (κ y) (τ (L x y))` in every cell.

Three stages, each an application of `decompose` (Baranyai rounding):
1. distribute each row class of the outline over its rows;
2. give every cell a symbol class;
3. split each symbol class into its symbols (perfect matchings).

> Adapted from `jtraverso/forbidden-latin-squares` @ e174838 (`FLS/Construct.lean`), same author.
> `FLS.realize` had `K = ZMod 3` and a fixed forbidden pattern; otherwise the proof is unchanged.
-/

@[expose] public section

namespace CDRBicolour.KBicolor.Hilton

open Finset

/-- A natural-valued vector with total one is an indicator. -/
theorem eq_of_sum_eq_one {ι : Type*} [Fintype ι] {v : ι → ℕ} (hv : ∑ i, v i = 1) {i j : ι}
    (hi : 1 ≤ v i) (hj : 1 ≤ v j) : i = j := by
  classical
  by_contra hij
  have : v i + v j ≤ ∑ k, v k := by
    rw [← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

theorem exists_eq_one_of_sum_eq_one {ι : Type*} [Fintype ι] {v : ι → ℕ} (hv : ∑ i, v i = 1) :
    ∃ i, v i = 1 := by
  classical
  have hne : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hv
  obtain ⟨i, hi⟩ := hne
  refine ⟨i, ?_⟩
  have : v i ≤ ∑ k, v k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

theorem le_one_of_sum_eq_one {ι : Type*} [Fintype ι] {v : ι → ℕ} (hv : ∑ i, v i = 1) (i : ι) :
    v i ≤ 1 := by
  have : v i ≤ ∑ k, v k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

variable {α β γ K : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype K]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq K]

theorem realize (ok : K → K → K → Prop) (ρ : α → K) (κ : β → K) (τ : γ → K)
    (M : K → K → K → ℕ)
    (h1 : ∀ r c, ∑ s, M r c s = csize ρ r * csize κ c)
    (h2 : ∀ r s, ∑ c, M r c s = csize ρ r * csize τ s)
    (h3 : ∀ c s, ∑ r, M r c s = csize κ c * csize τ s)
    (h0 : ∀ r c s, ¬ ok r c s → M r c s = 0) :
    ∃ L : α → β → γ, (∀ x, Function.Bijective (L x)) ∧
      (∀ y, Function.Bijective (fun x => L x y)) ∧ ∀ x y, ok (ρ x) (κ y) (τ (L x y)) := by
  classical
  ------------------------------------------------------------------
  -- Stage 1: distribute each row class over its rows
  have st1 := fun r => decompose (csize ρ r) (M r) (fun c => csize κ c) (fun s => csize τ s)
    (h1 r) (h2 r)
  choose F hFr hFc hFs using st1
  set m : α → K → K → ℕ := spread ρ F with hm
  have m1 : ∀ x c, ∑ s, m x c s = csize κ c := by
    intro x c; rw [hm, spread_eq ρ F x (ρ x) rfl]; exact hFr _ _ c
  have m2 : ∀ x s, ∑ c, m x c s = csize τ s := by
    intro x s; rw [hm, spread_eq ρ F x (ρ x) rfl]; exact hFc _ _ s
  have m3 : ∀ c s, ∑ x, m x c s = csize κ c * csize τ s := by
    intro c s
    rw [hm, sum_spread ρ F (fun _ v => v c s), ← h3 c s]
    exact Finset.sum_congr rfl fun r _ => hFs r c s
  have m0 : ∀ x c s, ¬ ok (ρ x) c s → m x c s = 0 := by
    intro x c s hz
    have hle : m x c s ≤ M (ρ x) c s := by
      rw [hm, spread_eq ρ F x (ρ x) rfl, ← hFs (ρ x) c s]
      exact Finset.single_le_sum (f := fun t => F (ρ x) t c s) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ _)
    have := h0 _ _ _ hz
    omega
  ------------------------------------------------------------------
  -- Stage 2: give every cell a symbol class
  have st2 := fun c => decompose (I := α) (J := K) (csize κ c) (fun x s => m x c s)
    (fun _ => 1) (fun s => csize τ s) (fun x => by rw [m1 x c, mul_one]) (fun s => m3 c s)
  choose G hGr hGc hGs using st2
  set g : β → α → K → ℕ := spread κ G with hg
  have g1 : ∀ y x, ∑ s, g y x s = 1 := by
    intro y x; rw [hg, spread_eq κ G y (κ y) rfl]; exact hGr _ _ x
  have g2 : ∀ y s, ∑ x, g y x s = csize τ s := by
    intro y s; rw [hg, spread_eq κ G y (κ y) rfl]; exact hGc _ _ s
  have g3 : ∀ y x s, g y x s ≤ m x (κ y) s := by
    intro y x s
    rw [hg, spread_eq κ G y (κ y) rfl, ← hGs (κ y) x s]
    exact Finset.single_le_sum (f := fun t => G (κ y) t x s) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ _)
  have g4 : ∀ x s, ∑ y, g y x s = csize τ s := by
    intro x s
    rw [hg, sum_spread κ G (fun _ v => v x s), ← m2 x s]
    exact Finset.sum_congr rfl fun c _ => hGs c x s
  -- the class of a cell
  have hcls : ∀ x y, ∃ s, g y x s = 1 := fun x y => exists_eq_one_of_sum_eq_one (g1 y x)
  choose cls hcls1 using hcls
  have gcls : ∀ x y s, g y x s = if s = cls x y then 1 else 0 := by
    intro x y s
    split_ifs with h
    · rw [h]; exact hcls1 x y
    · have hle := le_one_of_sum_eq_one (g1 y x) s
      by_contra hne
      exact h (eq_of_sum_eq_one (g1 y x) (by omega) (by rw [hcls1 x y]))
  have cls_ok : ∀ x y, ok (ρ x) (κ y) (cls x y) := by
    intro x y
    by_contra hz
    have := g3 y x (cls x y)
    rw [hcls1 x y, m0 x _ _ hz] at this
    omega
  have cls_row : ∀ x s, (univ.filter fun y => cls x y = s).card = csize τ s := by
    intro x s
    rw [← g4 x s, Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [gcls x y s]
    by_cases h : cls x y = s
    · simp [h]
    · simp [h, Ne.symm h]
  have cls_col : ∀ y s, (univ.filter fun x => cls x y = s).card = csize τ s := by
    intro y s
    rw [← g2 y s, Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [gcls x y s]
    by_cases h : cls x y = s
    · simp [h]
    · simp [h, Ne.symm h]
  ------------------------------------------------------------------
  -- Stage 3: split each symbol class into its symbols
  set B : K → α → β → ℕ := fun s x y => if cls x y = s then 1 else 0 with hB
  have st3 := fun s => decompose (I := α) (J := β) (csize τ s) (B s) (fun _ => 1) (fun _ => 1)
    (fun x => by
      rw [mul_one, ← cls_row x s, Finset.card_eq_sum_ones, Finset.sum_filter])
    (fun y => by
      rw [mul_one, ← cls_col y s, Finset.card_eq_sum_ones, Finset.sum_filter])
  choose H hHr hHc hHs using st3
  set h : γ → α → β → ℕ := spread τ H with hh
  have h1' : ∀ z x, ∑ y, h z x y = 1 := by
    intro z x; rw [hh, spread_eq τ H z (τ z) rfl]; exact hHr _ _ x
  have h2' : ∀ z y, ∑ x, h z x y = 1 := by
    intro z y; rw [hh, spread_eq τ H z (τ z) rfl]; exact hHc _ _ y
  have h3' : ∀ s x y, ∑ z ∈ univ.filter (fun z => τ z = s), h z x y = B s x y := by
    intro s x y
    rw [hh, sum_spread_class τ H (fun v => v x y) s]
    exact hHs s x y
  -- a symbol occupying a cell lies in the class of the cell
  have hclass : ∀ z x y, 1 ≤ h z x y → τ z = cls x y := by
    intro z x y hz
    have hle : h z x y ≤ B (τ z) x y := by
      rw [← h3' (τ z) x y]
      exact Finset.single_le_sum (f := fun z => h z x y) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
    simp only [hB] at hle
    split_ifs at hle with hc
    · exact hc.symm
    · omega
  -- every cell carries exactly one symbol
  have hcell : ∀ x y, ∃ z, h z x y = 1 := by
    intro x y
    have hs : ∑ z ∈ univ.filter (fun z => τ z = cls x y), h z x y = 1 := by
      rw [h3' (cls x y) x y]; simp [hB]
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ univ.filter (fun z => τ z = cls x y), h z x y ≠ 0 := by
      by_contra hc
      push_neg at hc
      rw [Finset.sum_eq_zero hc] at hs
      omega
    exact ⟨z, by have := le_one_of_sum_eq_one (h1' z x) y; omega⟩
  have hcell_unique : ∀ x y z z', h z x y = 1 → h z' x y = 1 → z = z' := by
    intro x y z z' hz hz'
    have tz := hclass z x y (by omega)
    have tz' := hclass z' x y (by omega)
    have hs : ∑ z ∈ univ.filter (fun z => τ z = cls x y), h z x y = 1 := by
      rw [h3' (cls x y) x y]; simp [hB]
    by_contra hne
    have : h z x y + h z' x y ≤ ∑ z ∈ univ.filter (fun z => τ z = cls x y), h z x y := by
      rw [← Finset.sum_pair (f := fun w => h w x y) hne]
      refine Finset.sum_le_sum_of_subset ?_
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp [tz, tz']
    omega
  choose L hL using hcell
  have hL_iff : ∀ x y z, L x y = z ↔ h z x y = 1 := by
    intro x y z
    constructor
    · rintro rfl; exact hL x y
    · intro hz; exact hcell_unique x y _ _ (hL x y) hz
  refine ⟨L, ?_, ?_, ?_⟩
  · intro x
    have hinj : Function.Injective (L x) := by
      intro y y' hy
      have a := hL x y
      have b := hL x y'
      rw [hy] at a
      exact eq_of_sum_eq_one (h1' (L x y') x) (by omega) (by omega)
    refine ⟨hinj, fun z => ?_⟩
    obtain ⟨y, hy⟩ := exists_eq_one_of_sum_eq_one (h1' z x)
    exact ⟨y, (hL_iff x y z).mpr hy⟩
  · intro y
    have hinj : Function.Injective (fun x => L x y) := by
      intro x x' hx
      have a := hL x y
      have b := hL x' y
      simp only at hx
      rw [hx] at a
      exact eq_of_sum_eq_one (h2' (L x' y) y) (by omega) (by omega)
    refine ⟨hinj, fun z => ?_⟩
    obtain ⟨x, hx⟩ := exists_eq_one_of_sum_eq_one (h2' z y)
    exact ⟨x, (hL_iff x y z).mpr hx⟩
  · intro x y
    rw [hclass (L x y) x y (by rw [hL x y])]
    exact cls_ok x y

end CDRBicolour.KBicolor.Hilton
