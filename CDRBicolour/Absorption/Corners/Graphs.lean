/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic
public import CDRBicolour.Absorption.Corners.Defs

/-!
# Graphs with degrees `d + 2·[i < r]` on `ℤ/s` (item 3, corners)

The planted minority structure needs, in every class, a simple graph whose degrees are `d` or
`d + 2`, with exactly `r` vertices of the larger degree.  We build it on `ZMod s`:

* `cg T`: the circulant with jumps `T ⊆ [1, s/2)`, `2|T|`-regular (`cg_degree`);
* `dg h` (`s = 2h`): the diameter matching, `1`-regular (`dg_degree`);
* `zg r` (`r ≥ 3`): the zig-zag cycle on `{0, …, r−1}` (evens up, odds down), with jumps `1, 2`
  only, so it is edge-disjoint from circulants with jumps `≥ 3` (`zg_degree`);
* a switch `{a, b} ↦ {i, a}, {i, b}` raising the degree of `i` by `2` (`switch_degree`), used when
  `r ∈ {1, 2}` and `d ≥ 1` (for `d = 0`, `r ∈ {1, 2}` there is no such graph, and none is needed).
-/

@[expose] public section

noncomputable section

open Classical

namespace CDRBicolour.Absorption.Corners

open Finset SimpleGraph

variable {s : ℕ} [NeZero s]

/-! ### Casting -/

theorem cast_inj {i j : ℕ} (hi : i < s) (hj : j < s) (h : (i : ZMod s) = j) : i = j := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h

theorem cast_ne_zero {i : ℕ} (h0 : 0 < i) (hi : i < s) : (i : ZMod s) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

/-! ### Circulants -/

/-- The circulant with jumps `T`. -/
def cg (T : Finset ℕ) : SimpleGraph (ZMod s) :=
  circulantGraph ((T.image fun t : ℕ => (t : ZMod s) : Finset (ZMod s)) : Set (ZMod s))

theorem cg_adj {T : Finset ℕ} {u v : ZMod s} :
    (cg T).Adj u v ↔ u ≠ v ∧ ∃ t ∈ T, v = u + t ∨ u = v + t := by
  simp only [cg, circulantGraph_adj, coe_image, Set.mem_image, mem_coe]
  constructor
  · rintro ⟨h, (⟨t, ht, e⟩ | ⟨t, ht, e⟩)⟩
    · exact ⟨h, t, ht, Or.inr (by rw [e]; ring)⟩
    · exact ⟨h, t, ht, Or.inl (by rw [e]; ring)⟩
  · rintro ⟨h, t, ht, (e | e)⟩
    · exact ⟨h, Or.inr ⟨t, ht, by rw [e]; ring⟩⟩
    · exact ⟨h, Or.inl ⟨t, ht, by rw [e]; ring⟩⟩

/-- **Circulants are `2|T|`-regular.** -/
theorem cg_degree {T : Finset ℕ} (hT : ∀ t ∈ T, 1 ≤ t ∧ 2 * t < s) (u : ZMod s) :
    ((cg T).neighborSet u).ncard = 2 * #T := by
  rw [ncard_neighborSet]
  have hN : (cg T).neighborFinset u =
      (T.image fun t : ℕ => u + t) ∪ (T.image fun t : ℕ => u - t) := by
    ext v
    simp only [mem_neighborFinset, cg_adj, mem_union, mem_image]
    constructor
    · rintro ⟨-, t, ht, (e | e)⟩
      · exact Or.inl ⟨t, ht, e.symm⟩
      · exact Or.inr ⟨t, ht, by rw [e]; ring⟩
    · rintro (⟨t, ht, e⟩ | ⟨t, ht, e⟩)
      · have h0 := cast_ne_zero (s := s) (hT t ht).1 (by have := hT t ht; omega)
        refine ⟨fun h => h0 ?_, t, ht, Or.inl e.symm⟩
        rw [← e] at h; linear_combination -h
      · have h0 := cast_ne_zero (s := s) (hT t ht).1 (by have := hT t ht; omega)
        refine ⟨fun h => h0 ?_, t, ht, Or.inr (by rw [← e]; ring)⟩
        rw [← e] at h; linear_combination h
  have hinj : ∀ t ∈ T, ∀ t' ∈ T, (t : ZMod s) = t' → t = t' := fun t ht t' ht' h =>
    cast_inj (by have := hT t ht; omega) (by have := hT t' ht'; omega) h
  rw [← card_neighborFinset_eq_degree, hN, card_union_of_disjoint, card_image_of_injOn,
    card_image_of_injOn]
  · ring
  · intro t ht t' ht' h; exact hinj t ht t' ht' (by simpa using h)
  · intro t ht t' ht' h; exact hinj t ht t' ht' (by simpa using h)
  · rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hv
    obtain ⟨t', ht', e⟩ := mem_image.1 hv'
    have : ((t + t' : ℕ) : ZMod s) = 0 := by push_cast; linear_combination -e
    exact cast_ne_zero (s := s) (by have := hT t ht; omega)
      (by have := hT t ht; have := hT t' ht'; omega) this

/-! ### The diameter matching -/

/-- The diameter matching (for `s = 2h`). -/
def dg (h : ℕ) : SimpleGraph (ZMod s) := circulantGraph {(h : ZMod s)}

theorem dg_degree {h : ℕ} (hs : s = 2 * h) (h1 : 1 ≤ h) (u : ZMod s) :
    ((dg h).neighborSet u).ncard = 1 := by
  rw [ncard_neighborSet]
  have hh : ((h : ℕ) : ZMod s) + h = 0 := by
    rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]; exact ⟨1, by omega⟩
  have hN : (dg h).neighborFinset u = {u + h} := by
    ext v
    rw [mem_neighborFinset, mem_singleton]
    simp only [dg, circulantGraph_adj, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, (e | e)⟩
      · linear_combination -e - hh
      · linear_combination e
    · rintro rfl
      refine ⟨fun e => cast_ne_zero (s := s) (i := h) h1 (by omega) ?_, Or.inr (by ring)⟩
      linear_combination -e
  rw [← card_neighborFinset_eq_degree, hN, card_singleton]

/-! ### The zig-zag cycle on `{0, …, r−1}` -/

/-- The zig-zag relation on naturals: jumps `2`, plus the pairs `{0,1}` and `{r−2, r−1}`. -/
def zrel (r i j : ℕ) : Prop := i < r ∧ j < r ∧ (i + 2 = j ∨ j + 2 = i ∨ i + j = 1 ∨ i + j = 2 * r - 3)

theorem zrel_symm {r i j : ℕ} (h : zrel r i j) : zrel r j i := by
  obtain ⟨hi, hj, e⟩ := h
  exact ⟨hj, hi, by omega⟩

/-- The zig-zag cycle. -/
def zg (r : ℕ) : SimpleGraph (ZMod s) := SimpleGraph.fromRel fun x y => zrel r x.val y.val

theorem zg_adj {r : ℕ} {x y : ZMod s} : (zg r).Adj x y ↔ x ≠ y ∧ zrel r x.val y.val := by
  simp only [zg, fromRel_adj]
  constructor
  · rintro ⟨h, h' | h'⟩
    · exact ⟨h, h'⟩
    · exact ⟨h, zrel_symm h'⟩
  · rintro ⟨h, h'⟩; exact ⟨h, Or.inl h'⟩

/-- The zig-zag neighbours of `i` as naturals. -/
def zN (r i : ℕ) : Finset ℕ :=
  (range r).filter fun j => j ≠ i ∧ (i + 2 = j ∨ j + 2 = i ∨ i + j = 1 ∨ i + j = 2 * r - 3)

theorem zN_eq {r i : ℕ} (a b : ℕ)
    (h : ∀ j, (j < r ∧ j ≠ i ∧ (i + 2 = j ∨ j + 2 = i ∨ i + j = 1 ∨ i + j = 2 * r - 3)) ↔
      (j = a ∨ j = b)) : zN r i = {a, b} := by
  ext j; simp only [zN, mem_filter, mem_range, mem_insert, mem_singleton]; exact h j

theorem zN_card {r i : ℕ} (hr : 3 ≤ r) (hi : i < r) : #(zN r i) = 2 := by
  rcases Nat.lt_or_ge i 2 with h2 | h2
  · rcases Nat.lt_or_ge i 1 with h1 | h1
    · rw [zN_eq 1 2 (fun j => by omega)]; rfl
    · rcases Nat.lt_or_ge r 4 with hr4 | hr4
      · rw [zN_eq 0 2 (fun j => by omega)]; rfl
      · rw [zN_eq 0 3 (fun j => by omega)]; rfl
  · rcases Nat.lt_or_ge (i + 3) (r + 1) with hm | hm
    · rw [zN_eq (i - 2) (i + 2) (fun j => by omega)]; exact card_pair (by omega)
    · rcases Nat.lt_or_ge (i + 2) (r + 1) with hm' | hm'
      · rw [zN_eq (i - 2) (r - 1) (fun j => by omega)]; exact card_pair (by omega)
      · rw [zN_eq (i - 2) (r - 2) (fun j => by omega)]; exact card_pair (by omega)

theorem val_lt (x : ZMod s) : x.val < s := ZMod.val_lt x

theorem zg_nbr {r : ℕ} (hrs : r ≤ s) (x : ZMod s) :
    (zg r).neighborFinset x = if x.val < r then (zN r x.val).image (Nat.cast) else ∅ := by
  ext y
  rw [mem_neighborFinset, zg_adj]
  simp only [zrel]
  split_ifs with hx
  · simp only [zN, mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨hne, -, hy, h⟩
      refine ⟨y.val, ⟨hy, fun e => hne (ZMod.val_injective _ e.symm), h⟩, ZMod.natCast_zmod_val y⟩
    · rintro ⟨j, ⟨hj, hne, h⟩, rfl⟩
      have hjv : ((j : ZMod s)).val = j := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      rw [hjv]
      exact ⟨fun e => hne (by rw [← hjv, ← e]), hx, hj, h⟩
  · simp only [notMem_empty, iff_false, not_and]
    intro _ h; exact absurd h hx

/-- **The zig-zag cycle has degree `2` on `{0, …, r−1}` and `0` elsewhere.** -/
theorem zg_degree {r : ℕ} (hr : 3 ≤ r) (hrs : r ≤ s) (x : ZMod s) :
    ((zg r).neighborSet x).ncard = if x.val < r then 2 else 0 := by
  rw [ncard_neighborSet, ← card_neighborFinset_eq_degree, zg_nbr hrs]
  split_ifs with hx
  · rw [card_image_of_injOn, zN_card hr hx]
    intro j hj j' hj' e
    simp only [zN, coe_filter, mem_range, Set.mem_setOf_eq] at hj hj'
    exact cast_inj (by omega) (by omega) e
  · rfl

/-- Zig-zag edges join points at distance `1` or `2`. -/
theorem zg_adj_diff {r : ℕ} (hrs : r ≤ s) {x y : ZMod s} (h : (zg r).Adj x y) :
    ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ (y = x + k ∨ x = y + k) := by
  obtain ⟨hne, hx, hy, e⟩ := zg_adj.1 h
  have hv : x.val ≠ y.val := fun e => hne (ZMod.val_injective _ e)
  have ex := ZMod.natCast_zmod_val x
  have ey := ZMod.natCast_zmod_val y
  rcases e with e | e | e | e
  · exact ⟨2, Or.inr rfl, Or.inl (by rw [← ex, ← ey, ← e]; push_cast; ring)⟩
  · exact ⟨2, Or.inr rfl, Or.inr (by rw [← ex, ← ey, ← e]; push_cast; ring)⟩
  · rcases (show x.val = 0 ∧ y.val = 1 ∨ x.val = 1 ∧ y.val = 0 by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨1, Or.inl rfl, Or.inl (by rw [← ex, ← ey, h1, h2]; push_cast; ring)⟩
    · exact ⟨1, Or.inl rfl, Or.inr (by rw [← ex, ← ey, h1, h2]; push_cast; ring)⟩
  · rcases (show x.val + 1 = y.val ∨ y.val + 1 = x.val by omega) with h1 | h1
    · exact ⟨1, Or.inl rfl, Or.inl (by rw [← ex, ← ey, ← h1]; push_cast; ring)⟩
    · exact ⟨1, Or.inl rfl, Or.inr (by rw [← ex, ← ey, ← h1]; push_cast; ring)⟩

/-! ### Switches -/

section Switch

variable {W : Type*} [Fintype W]

/-- The switch: delete `pq`, add `ip` and `iq`. -/
def sw (B : SimpleGraph W) (i p q : W) : SimpleGraph W :=
  B.deleteEdges {s(p, q)} ⊔ fromEdgeSet {s(i, p), s(i, q)}

theorem sw_adj {B : SimpleGraph W} {i p q v w : W} :
    (sw B i p q).Adj v w ↔ (B.Adj v w ∧ ¬((v = p ∧ w = q) ∨ (v = q ∧ w = p))) ∨
      (((v = i ∧ w = p) ∨ (v = p ∧ w = i) ∨ (v = i ∧ w = q) ∨ (v = q ∧ w = i)) ∧ v ≠ w) := by
  simp only [sw, sup_adj, deleteEdges_adj, fromEdgeSet_adj, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sym2.eq_iff]
  tauto

/-- **The switch raises the degree of `i` by two and keeps every other degree.** -/
theorem sw_degree {B : SimpleGraph W} {i p q : W} (hip : i ≠ p) (hiq : i ≠ q) (hpq : B.Adj p q)
    (nip : ¬ B.Adj i p) (niq : ¬ B.Adj i q) (v : W) :
    ((sw B i p q).neighborSet v).ncard = (B.neighborSet v).ncard + if v = i then 2 else 0 := by
  rw [ncard_neighborSet, ncard_neighborSet]
  have hpq' : p ≠ q := hpq.ne
  have hqp := hpq.symm
  have nip' : ¬ B.Adj p i := fun h => nip h.symm
  have niq' : ¬ B.Adj q i := fun h => niq h.symm
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  by_cases hv : v = i
  · subst hv
    have hN : (sw B v p q).neighborFinset v = insert p (insert q (B.neighborFinset v)) := by
      ext w
      simp only [mem_neighborFinset, sw_adj, mem_insert]
      constructor
      · intro h; aesop
      · intro h; aesop
    rw [hN, card_insert_of_notMem, card_insert_of_notMem, if_pos rfl]
    · simpa [mem_neighborFinset] using niq
    · simp only [mem_insert, mem_neighborFinset, not_or]; exact ⟨hpq', nip⟩
  rw [if_neg hv, add_zero]
  by_cases hp : v = p
  · subst hp
    have hN : (sw B i v q).neighborFinset v = insert i ((B.neighborFinset v).erase q) := by
      ext w
      simp only [mem_neighborFinset, sw_adj, mem_insert, mem_erase]
      constructor
      · intro h; aesop
      · intro h; aesop
    rw [hN, card_insert_of_notMem, card_erase_of_mem (by simpa [mem_neighborFinset] using hpq)]
    · have : 0 < #(B.neighborFinset v) := card_pos.2 ⟨q, by simpa [mem_neighborFinset] using hpq⟩
      omega
    · simp only [mem_erase, mem_neighborFinset, not_and]
      exact fun _ h => nip h.symm
  by_cases hq : v = q
  · subst hq
    have hN : (sw B i p v).neighborFinset v = insert i ((B.neighborFinset v).erase p) := by
      ext w
      simp only [mem_neighborFinset, sw_adj, mem_insert, mem_erase]
      constructor
      · intro h; aesop
      · intro h; aesop
    rw [hN, card_insert_of_notMem, card_erase_of_mem (by simpa [mem_neighborFinset] using hqp)]
    · have : 0 < #(B.neighborFinset v) := card_pos.2 ⟨p, by simpa [mem_neighborFinset] using hqp⟩
      omega
    · simp only [mem_erase, mem_neighborFinset, not_and]
      exact fun _ h => niq h.symm
  · congr 1
    ext w
    simp only [mem_neighborFinset, sw_adj]
    constructor
    · intro h; aesop
    · intro h; aesop

end Switch

/-! ### The graph with degrees `d + 2·[i < r]` -/

theorem degree_sup_disj {W : Type*} [Fintype W] {G H : SimpleGraph W} (h : Disjoint G H) (v : W) :
    ((G ⊔ H).neighborSet v).ncard = (G.neighborSet v).ncard + (H.neighborSet v).ncard := by
  rw [neighborSet_sup, Set.ncard_union_eq (disjoint_neighborSet.mpr h v) (Set.toFinite _)
    (Set.toFinite _)]

/-- Two jumps `k ≠ t` with `k + t ≠ s` never join the same pair. -/
theorem jumps_ne {k t : ℕ} (hk : 0 < k) (hks : k < s) (ht : 0 < t) (hts : t < s) (hkt : k ≠ t)
    (hsum : k + t ≠ s) {x y : ZMod s} (h1 : y = x + k ∨ x = y + k) (h2 : y = x + t ∨ x = y + t) :
    False := by
  have e1 : ∀ {a b : ℕ}, 0 < a → 0 < b → a < s → b < s → a + b ≠ s →
      ((a : ZMod s) + b = 0) → False := fun ha hb has hbs hab e => by
    rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff] at e
    obtain ⟨c, hc⟩ := e
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact hkt (cast_inj hks hts (by linear_combination h2 - h1))
  · exact e1 hk ht hks hts hsum (by linear_combination -h1 - h2)
  · exact e1 hk ht hks hts hsum (by linear_combination -h1 - h2)
  · exact hkt (cast_inj hks hts (by linear_combination h2 - h1))

theorem dg_eq (h : ℕ) : (dg h : SimpleGraph (ZMod s)) = cg {h} := by
  simp [dg, cg]

/-- Natural-number form of a circulant adjacency between casts. -/
theorem cg_adj_nat {U : Finset ℕ} (hU : ∀ t ∈ U, t < s) {x y : ℕ} (hx : x < s) (hy : y < s)
    (h : (cg U).Adj (x : ZMod s) (y : ZMod s)) :
    ∃ t ∈ U, y = x + t ∨ y + s = x + t ∨ x = y + t ∨ x + s = y + t := by
  obtain ⟨-, t, ht, e⟩ := cg_adj.1 h
  have hts := hU t ht
  have key : ∀ {a b : ℕ}, a < s → b < s → ((b : ZMod s) = a + t) → b = a + t ∨ b + s = a + t := by
    intro a b ha hb e
    rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hb] at e
    rcases Nat.lt_or_ge (a + t) s with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at e; omega
    · rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)] at e; omega
  rcases e with e | e
  · rcases key hx hy e with e' | e'
    · exact ⟨t, ht, Or.inl e'⟩
    · exact ⟨t, ht, Or.inr (Or.inl e')⟩
  · rcases key hy hx e with e' | e'
    · exact ⟨t, ht, Or.inr (Or.inr (Or.inl e'))⟩
    · exact ⟨t, ht, Or.inr (Or.inr (Or.inr e'))⟩

theorem cg_adj_shift {U : Finset ℕ} {τ : ℕ} (hτ : τ ∈ U) (hτ0 : 0 < τ) (hτs : τ < s) (a : ℕ) :
    (cg U).Adj (a : ZMod s) ((a + τ : ℕ) : ZMod s) := by
  rw [cg_adj]
  refine ⟨fun e => cast_ne_zero (s := s) hτ0 hτs ?_, τ, hτ, Or.inl (by push_cast; ring)⟩
  push_cast at e; linear_combination -e

theorem val_lt_two {x : ZMod s} (hs : 2 ≤ s) : x.val < 2 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have ex := ZMod.natCast_zmod_val x
    rcases (show x.val = 0 ∨ x.val = 1 by omega) with e | e
    · left; rw [← ex, e]; simp
    · right; rw [← ex, e]; simp
  · rintro (rfl | rfl)
    · rw [ZMod.val_zero]; omega
    · rw [ZMod.val_one'' (by omega)]; omega

/-- **Existence of the planted graph of one class.** -/
theorem exists_graph {d r : ℕ} (hs : 4 * d + 64 ≤ s) (hr : r < s) (hodd : d % 2 = 1 → s % 2 = 0)
    (hex : ¬ (d = 0 ∧ (r = 1 ∨ r = 2))) :
    ∃ G : SimpleGraph (ZMod s), ∀ x, (G.neighborSet x).ncard = d + if x.val < r then 2 else 0 := by
  obtain ⟨j, hj⟩ : ∃ j, j = d / 2 := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, h = s / 2 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = Icc 3 (j + 2) := ⟨_, rfl⟩
  have hTc : #T = j := by simp [hT]
  have hTb : ∀ t ∈ T, 3 ≤ t ∧ t ≤ j + 2 := fun t ht => by simpa [hT] using ht
  have hT' : ∀ t ∈ T, 1 ≤ t ∧ 2 * t < s := fun t ht => by have := hTb t ht; omega
  -- the base: circulant plus diameter
  obtain ⟨U, hU⟩ : ∃ U : Finset ℕ, U = if d % 2 = 1 then T ∪ {h} else T := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : SimpleGraph (ZMod s), B = cg T ⊔ (if d % 2 = 1 then cg {h} else ⊥) :=
    ⟨_, rfl⟩
  have hBdisj : Disjoint (cg T) (if d % 2 = 1 then cg ({h} : Finset ℕ) else (⊥ : SimpleGraph (ZMod s))) := by
    split_ifs with hd
    · rw [SimpleGraph.disjoint_left]
      intro x y h1 h2
      obtain ⟨-, t, ht, e1⟩ := cg_adj.1 h1
      obtain ⟨-, t', ht', e2⟩ := cg_adj.1 h2
      rw [mem_singleton] at ht'; rw [ht'] at e2
      have := hTb t ht
      exact jumps_ne (s := s) (k := t) (t := h) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) e1 e2
    · exact disjoint_bot_right
  have hBdeg : ∀ x, (B.neighborSet x).ncard = d := by
    intro x
    rw [hB, degree_sup_disj hBdisj, cg_degree hT', hTc]
    split_ifs with hd
    · rw [← dg_eq, dg_degree (by omega) (by omega)]; omega
    · rw [show (⊥ : SimpleGraph (ZMod s)).neighborSet x = ∅ by ext; simp, Set.ncard_empty]; omega
  have hBadj : ∀ {x y : ZMod s}, B.Adj x y → (cg U).Adj x y := by
    intro x y hxy
    rw [hB] at hxy
    rcases hxy with hxy | hxy
    · obtain ⟨hne, t, ht, e⟩ := cg_adj.1 hxy
      exact cg_adj.2 ⟨hne, t, by rw [hU]; split_ifs <;> simp [ht], e⟩
    · split_ifs at hxy with hd
      · obtain ⟨hne, t, ht, e⟩ := cg_adj.1 hxy
        exact cg_adj.2 ⟨hne, t, by rw [hU, if_pos hd]; simp at ht ⊢; simp [ht], e⟩
      · exact absurd hxy (by simp)
  have hUb : ∀ t ∈ U, (3 ≤ t ∧ t ≤ j + 2) ∨ t = h := by
    intro t ht
    rw [hU] at ht
    split_ifs at ht
    · rcases mem_union.1 ht with ht | ht
      · exact Or.inl (hTb t ht)
      · exact Or.inr (mem_singleton.1 ht)
    · exact Or.inl (hTb t ht)
  have hUs : ∀ t ∈ U, t < s := fun t ht => by rcases hUb t ht with h' | h' <;> omega
  -- non-adjacency to small points far from the jumps
  have nadj : ∀ {x y : ℕ}, x < s → y < s → (∀ t ∈ U, y ≠ x + t ∧ y + s ≠ x + t ∧ x ≠ y + t ∧
      x + s ≠ y + t) → ¬ B.Adj (x : ZMod s) (y : ZMod s) := by
    intro x y hx hy hc hxy
    obtain ⟨t, ht, e⟩ := cg_adj_nat hUs hx hy (hBadj hxy)
    have := hc t ht; omega
  by_cases hr0 : r = 0
  · exact ⟨B, fun x => by rw [hBdeg]; simp [hr0]⟩
  by_cases hr3 : 3 ≤ r
  · -- add the zig-zag cycle
    have hdisj : Disjoint B (zg r) := by
      rw [SimpleGraph.disjoint_left]
      intro x y h1 h2
      obtain ⟨hne, t, ht, e1⟩ := cg_adj.1 (hBadj h1)
      obtain ⟨k, hk, e2⟩ := zg_adj_diff (by omega) h2
      have := hUb t ht
      rcases hk with rfl | rfl
      · exact jumps_ne (s := s) (k := 1) (t := t) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) e2 e1
      · exact jumps_ne (s := s) (k := 2) (t := t) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) e2 e1
    refine ⟨B ⊔ zg r, fun x => ?_⟩
    rw [degree_sup_disj hdisj, hBdeg, zg_degree hr3 (by omega)]
  -- `r ∈ {1, 2}` and `d ≥ 1`: switches
  have hd1 : 1 ≤ d := by omega
  obtain ⟨τ, hτ⟩ : ∃ τ : ℕ, τ = if 2 ≤ d then 3 else h := ⟨_, rfl⟩
  have hτb : 3 ≤ τ ∧ τ ≤ h := by rw [hτ]; split_ifs <;> omega
  have hτc : (2 ≤ d ∧ τ = 3) ∨ (d < 2 ∧ τ = h ∧ s % 2 = 0) := by
    rw [hτ]; split_ifs with h2
    · exact Or.inl ⟨h2, rfl⟩
    · exact Or.inr ⟨by omega, rfl, hodd (by omega)⟩
  have hτU : τ ∈ U := by
    rcases hτc with ⟨h2, e⟩ | ⟨h2, e, -⟩
    · rw [e, hU]; split_ifs <;> simp only [hT, mem_union, mem_Icc, mem_singleton] <;> omega
    · rw [e, hU, if_pos (by omega)]; simp
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = j + 10 := ⟨_, rfl⟩
  have Ba : B.Adj (a : ZMod s) ((a + τ : ℕ) : ZMod s) := by
    have := cg_adj_shift (s := s) hτU (by omega) (by omega) a
    rw [hB]
    rw [hU] at hτU
    by_cases hd : d % 2 = 1
    · rw [if_pos hd] at hτU ⊢
      rcases mem_union.1 hτU with h' | h'
      · exact Or.inl (cg_adj_shift h' (by omega) (by omega) a)
      · exact Or.inr (cg_adj_shift h' (by omega) (by omega) a)
    · rw [if_neg hd] at hτU ⊢
      exact Or.inl (cg_adj_shift hτU (by omega) (by omega) a)
  have n0a : ¬ B.Adj ((0 : ℕ) : ZMod s) (a : ZMod s) :=
    nadj (by omega) (by omega) fun t ht => by have := hUb t ht; omega
  have n0b : ¬ B.Adj ((0 : ℕ) : ZMod s) ((a + τ : ℕ) : ZMod s) :=
    nadj (by omega) (by omega) fun t ht => by have := hUb t ht; omega
  have c0a : ((0 : ℕ) : ZMod s) ≠ (a : ZMod s) := fun e => by
    have := cast_inj (s := s) (by omega) (by omega) e; omega
  have c0b : ((0 : ℕ) : ZMod s) ≠ ((a + τ : ℕ) : ZMod s) := fun e => by
    have := cast_inj (s := s) (by omega) (by omega) e; omega
  obtain ⟨G1, hG1d⟩ : ∃ G1, G1 = sw B ((0 : ℕ) : ZMod s) (a : ZMod s) ((a + τ : ℕ) : ZMod s) :=
    ⟨_, rfl⟩
  have hG1 := sw_degree c0a c0b Ba n0a n0b
  rw [← hG1d] at hG1
  rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl
  · refine ⟨G1, fun x => ?_⟩
    rw [hG1, hBdeg]
    congr 1
    have : x.val < 1 ↔ x = ((0 : ℕ) : ZMod s) := by
      rw [Nat.cast_zero, Nat.lt_one_iff, ZMod.val_eq_zero]
    by_cases hx : x = ((0 : ℕ) : ZMod s)
    · rw [if_pos hx, if_pos (this.2 hx)]
    · rw [if_neg hx, if_neg (fun h' => hx (this.1 h'))]
  · obtain ⟨b, hb⟩ : ∃ b : ℕ, b = j + 20 := ⟨_, rfl⟩
    have G1b : G1.Adj (b : ZMod s) ((b + τ : ℕ) : ZMod s) := by
      rw [hG1d, sw_adj]
      left
      refine ⟨?_, ?_⟩
      · rw [hB]
        rw [hU] at hτU
        by_cases hd : d % 2 = 1
        · rw [if_pos hd] at hτU ⊢
          rcases mem_union.1 hτU with h' | h'
          · exact Or.inl (cg_adj_shift h' (by omega) (by omega) b)
          · exact Or.inr (cg_adj_shift h' (by omega) (by omega) b)
        · rw [if_neg hd] at hτU ⊢
          exact Or.inl (cg_adj_shift hτU (by omega) (by omega) b)
      · rintro (⟨e, -⟩ | ⟨e, -⟩)
        · have := cast_inj (s := s) (by omega) (by omega) e; omega
        · have := cast_inj (s := s) (by omega) (by omega) e; omega
    have n1 : ∀ {y : ℕ}, y < s → 10 ≤ y → y ≠ a → y ≠ a + τ →
        (∀ t ∈ U, y ≠ 1 + t ∧ y + s ≠ 1 + t ∧ 1 ≠ y + t ∧ 1 + s ≠ y + t) →
        ¬ G1.Adj ((1 : ℕ) : ZMod s) (y : ZMod s) := by
      intro y hy h10 hya hyb hc hadj
      rw [hG1d, sw_adj] at hadj
      rcases hadj with ⟨hadj, -⟩ | ⟨hc', -⟩
      · exact nadj (by omega) hy hc hadj
      · rcases hc' with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
        · have := cast_inj (s := s) (by omega) (by omega) e; omega
        · have := cast_inj (s := s) (by omega) (by omega) e; omega
        · have := cast_inj (s := s) (by omega) (by omega) e; omega
        · have := cast_inj (s := s) (by omega) (by omega) e; omega
    have n1b := n1 (y := b) (by omega) (by omega) (by omega) (by omega)
      (fun t ht => by have := hUb t ht; omega)
    have n1c := n1 (y := b + τ) (by omega) (by omega) (by omega) (by omega)
      (fun t ht => by have := hUb t ht; omega)
    have c1b : ((1 : ℕ) : ZMod s) ≠ (b : ZMod s) := fun e => by
      have := cast_inj (s := s) (by omega) (by omega) e; omega
    have c1c : ((1 : ℕ) : ZMod s) ≠ ((b + τ : ℕ) : ZMod s) := fun e => by
      have := cast_inj (s := s) (by omega) (by omega) e; omega
    refine ⟨sw G1 ((1 : ℕ) : ZMod s) (b : ZMod s) ((b + τ : ℕ) : ZMod s), fun x => ?_⟩
    rw [sw_degree c1b c1c G1b n1b n1c, hG1, hBdeg]
    have h01 : ((0 : ℕ) : ZMod s) ≠ ((1 : ℕ) : ZMod s) := fun e => by
      have := cast_inj (s := s) (by omega) (by omega) e; omega
    have key : x.val < 2 ↔ (x = 0 ∨ x = 1) := val_lt_two (by omega)
    simp only [Nat.cast_zero, Nat.cast_one] at h01 ⊢
    by_cases hx0 : x = 0
    · rw [if_pos hx0, if_neg (by rw [hx0]; exact h01), if_pos (key.2 (Or.inl hx0))]
    · by_cases hx1 : x = 1
      · rw [if_neg hx0, if_pos hx1, if_pos (key.2 (Or.inr hx1))]
      · rw [if_neg hx0, if_neg hx1, if_neg (fun h' => by
          rcases key.1 h' with e | e
          · exact hx0 e
          · exact hx1 e)]

end CDRBicolour.Absorption.Corners
