/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Refined.Lattice

/-!
# Shift maps inside the colour classes (refined H1, item 2b)

On `Fin (a+b+c)` with the interval classes of `col3`, the shift
`τ_{δ,f,k}(v) = s + ((v − s + δ + 6k) mod ℓ_f)`, where `s` is the start of the class of `v` and
`ℓ_f = 6⌊len/6⌋ − 6f`, keeps the colour, adds `δ` to `v mod 6`, has fibres of size `≤ 2` and
takes `7` distinct values for `k < 7`.  For every triangle `{x,y,z}` some `f < 4`, `k < 7` make
`τ x, τ y, τ z` pairwise distinct and outside `{x,y,z}` (`exists_good_shift`), so the octahedron
on `x, y, z, τx, τy, τz` is genuine.  All classes are assumed to have at least `96` points.
-/

@[expose] public section

namespace CDRBicolour.Absorption.Refined

open Finset CDRBicolour.Prefix

variable {a b c : ℕ}

/-- Start of a class. -/
def cstart (a b c : ℕ) (X : Fin 3) : ℕ := if X = 0 then 0 else if X = 1 then a else a + b

/-- Length of a class. -/
def clen (a b c : ℕ) (X : Fin 3) : ℕ := if X = 0 then a else if X = 1 then b else c

/-- The modulus of family `f`. -/
def mdl (a b c : ℕ) (X : Fin 3) (f : ℕ) : ℕ := 6 * (clen a b c X / 6) - 6 * f

theorem class_bounds (v : Fin (a + b + c)) :
    cstart a b c (col3 a b c v) ≤ v.val ∧
      v.val < cstart a b c (col3 a b c v) + clen a b c (col3 a b c v) := by
  have := v.isLt
  unfold col3 cstart clen
  split_ifs <;> simp_all <;> omega

theorem class_end (X : Fin 3) : cstart a b c X + clen a b c X ≤ a + b + c := by
  unfold cstart clen; fin_cases X <;> simp <;> omega

theorem col3_of_mem {X : Fin 3} {u : ℕ} (hu : u < a + b + c) (h1 : cstart a b c X ≤ u)
    (h2 : u < cstart a b c X + clen a b c X) : col3 a b c ⟨u, hu⟩ = X := by
  unfold col3; simp only [cstart, clen] at h1 h2
  fin_cases X <;> simp_all <;> split_ifs <;> first | rfl | omega

/-- Large classes. -/
def BigCls (a b c : ℕ) : Prop := 96 ≤ a ∧ 96 ≤ b ∧ 96 ≤ c

theorem clen_ge (h : BigCls a b c) (X : Fin 3) : 96 ≤ clen a b c X := by
  unfold clen; obtain ⟨h1, h2, h3⟩ := h; fin_cases X <;> simp <;> omega

/-- Facts on the modulus: `ℓ = 6 m`, `len − 23 ≤ ℓ ≤ len`. -/
theorem mdl_facts (h : BigCls a b c) (X : Fin 3) {f : ℕ} (hf : f < 4) :
    ∃ m, mdl a b c X f = 6 * m ∧ clen a b c X ≤ mdl a b c X f + 23 ∧
      mdl a b c X f ≤ clen a b c X := by
  have hl := clen_ge h X
  refine ⟨clen a b c X / 6 - f, ?_, ?_, ?_⟩ <;> unfold mdl <;> omega

/-- The shift. -/
def tau (a b c : ℕ) (δ f k : ℕ) (v : Fin (a + b + c)) : Fin (a + b + c) :=
  if hℓ : 0 < mdl a b c (col3 a b c v) f then
    ⟨cstart a b c (col3 a b c v) +
        (v.val - cstart a b c (col3 a b c v) + δ + 6 * k) % mdl a b c (col3 a b c v) f, by
      have h1 := Nat.mod_lt (v.val - cstart a b c (col3 a b c v) + δ + 6 * k) hℓ
      have h2 := class_end (a := a) (b := b) (c := c) (col3 a b c v)
      have h3 : mdl a b c (col3 a b c v) f ≤ clen a b c (col3 a b c v) := by unfold mdl; omega
      omega⟩
  else v

/-- Explicit value of the shift (`δ < 6`, `f < 4`, `k < 7`). -/
theorem tau_val (h : BigCls a b c) {δ f k : ℕ} (hδ : δ < 6) (hf : f < 4) (hk : k < 7)
    (v : Fin (a + b + c)) :
    (tau a b c δ f k v).val =
      if v.val - cstart a b c (col3 a b c v) + δ + 6 * k < mdl a b c (col3 a b c v) f then
        cstart a b c (col3 a b c v) + (v.val - cstart a b c (col3 a b c v) + δ + 6 * k)
      else cstart a b c (col3 a b c v) + (v.val - cstart a b c (col3 a b c v) + δ + 6 * k) -
        mdl a b c (col3 a b c v) f := by
  obtain ⟨m, hm, h1, h2⟩ := mdl_facts h (col3 a b c v) hf
  have hl := clen_ge h (col3 a b c v)
  have hb := class_bounds v
  have hℓ : 0 < mdl a b c (col3 a b c v) f := by omega
  unfold tau
  rw [dif_pos hℓ]
  show cstart a b c (col3 a b c v) +
      (v.val - cstart a b c (col3 a b c v) + δ + 6 * k) % mdl a b c (col3 a b c v) f = _
  split_ifs with hx
  · rw [Nat.mod_eq_of_lt hx]
  · have hx2 : v.val - cstart a b c (col3 a b c v) + δ + 6 * k - mdl a b c (col3 a b c v) f <
        mdl a b c (col3 a b c v) f := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hx2]
    omega

theorem tau_col (h : BigCls a b c) {δ f k : ℕ} (hδ : δ < 6) (hf : f < 4) (hk : k < 7)
    (v : Fin (a + b + c)) : col3 a b c (tau a b c δ f k v) = col3 a b c v := by
  have hv := tau_val h hδ hf hk v
  obtain ⟨m, hm, h1, h2⟩ := mdl_facts h (col3 a b c v) hf
  have hb := class_bounds v
  have hl := clen_ge h (col3 a b c v)
  have : tau a b c δ f k v = ⟨(tau a b c δ f k v).val, (tau a b c δ f k v).isLt⟩ := rfl
  rw [this]
  apply col3_of_mem
  · split_ifs at hv <;> omega
  · split_ifs at hv <;> omega

theorem tau_mod (h : BigCls a b c) {δ f k : ℕ} (hδ : δ < 6) (hf : f < 4) (hk : k < 7)
    (v : Fin (a + b + c)) : (tau a b c δ f k v).val % 6 = (v.val + δ) % 6 := by
  have hv := tau_val h hδ hf hk v
  obtain ⟨m, hm, h1, h2⟩ := mdl_facts h (col3 a b c v) hf
  have hb := class_bounds v
  split_ifs at hv <;> omega

/-- Two points with the same shift are equal or at distance exactly `ℓ_f` in one class. -/
theorem tau_eq (h : BigCls a b c) {δ f k : ℕ} (hδ : δ < 6) (hf : f < 4) (hk : k < 7)
    {v w : Fin (a + b + c)} (he : tau a b c δ f k v = tau a b c δ f k w) :
    v = w ∨ (col3 a b c v = col3 a b c w ∧
      (v.val + mdl a b c (col3 a b c v) f = w.val ∨
        w.val + mdl a b c (col3 a b c v) f = v.val)) := by
  have hc : col3 a b c v = col3 a b c w := by
    rw [← tau_col h hδ hf hk v, ← tau_col h hδ hf hk w, he]
  have hv := tau_val h hδ hf hk v
  have hw := tau_val h hδ hf hk w
  have hb := class_bounds v
  have hb' := class_bounds w
  obtain ⟨m, hm, h1, h2⟩ := mdl_facts h (col3 a b c v) hf
  rw [← hc] at hw hb'
  have hval : (tau a b c δ f k v).val = (tau a b c δ f k w).val := by rw [he]
  by_cases hvw : v = w
  · exact Or.inl hvw
  right
  refine ⟨hc, ?_⟩
  have hne : v.val ≠ w.val := fun e => hvw (Fin.ext e)
  split_ifs at hv hw <;> omega

/-- Seven distinct values. -/
theorem tau_inj_k (h : BigCls a b c) {δ f k k' : ℕ} (hδ : δ < 6) (hf : f < 4) (hk : k < 7)
    (hk' : k' < 7) (v : Fin (a + b + c)) (he : tau a b c δ f k v = tau a b c δ f k' v) :
    k = k' := by
  have hv := tau_val h hδ hf hk v
  have hv' := tau_val h hδ hf hk' v
  have hb := class_bounds v
  obtain ⟨m, hm, h1, h2⟩ := mdl_facts h (col3 a b c v) hf
  have hl := clen_ge h (col3 a b c v)
  have hval : (tau a b c δ f k v).val = (tau a b c δ f k' v).val := by rw [he]
  split_ifs at hv hv' <;> omega

/-- The shift moves every point when `δ ≢ 0`. -/
theorem tau_ne (h : BigCls a b c) {δ f k : ℕ} (hδ : δ < 6) (hδ0 : 0 < δ) (hf : f < 4) (hk : k < 7)
    (v : Fin (a + b + c)) : tau a b c δ f k v ≠ v := by
  intro he
  have := tau_mod h hδ hf hk v
  rw [he] at this
  omega

/-- Fibres have at most two points. -/
theorem card_fibre (h : BigCls a b c) {δ f k : ℕ} (hδ : δ < 6) (hf : f < 4) (hk : k < 7)
    (p : Fin (a + b + c)) : #(univ.filter fun v => tau a b c δ f k v = p) ≤ 2 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨S, hS, hS3⟩ := exists_subset_card_eq (show 3 ≤ #(univ.filter fun v => tau a b c δ f k v = p) by omega)
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := card_eq_three.1 hS3
  have hu : tau a b c δ f k u = p := (mem_filter.1 (hS (by simp))).2
  have hv : tau a b c δ f k v = p := (mem_filter.1 (hS (by simp))).2
  have hw : tau a b c δ f k w = p := (mem_filter.1 (hS (by simp))).2
  rcases tau_eq h hδ hf hk (hu.trans hv.symm) with e1 | ⟨c1, d1⟩
  · exact huv e1
  rcases tau_eq h hδ hf hk (hu.trans hw.symm) with e2 | ⟨c2, d2⟩
  · exact huw e2
  rcases tau_eq h hδ hf hk (hv.trans hw.symm) with e3 | ⟨c3, d3⟩
  · exact hvw e3
  rw [← c1] at d3
  have n1 : u.val ≠ v.val := fun e => huv (Fin.ext e)
  have n2 : u.val ≠ w.val := fun e => huw (Fin.ext e)
  have n3 : v.val ≠ w.val := fun e => hvw (Fin.ext e)
  omega

/-- A good shift for a triangle. -/
def GoodShift (a b c : ℕ) (δ f k : ℕ) (x y z : Fin (a + b + c)) : Prop :=
  tau a b c δ f k x ≠ tau a b c δ f k y ∧ tau a b c δ f k x ≠ tau a b c δ f k z ∧
    tau a b c δ f k y ≠ tau a b c δ f k z ∧
    tau a b c δ f k x ≠ y ∧ tau a b c δ f k x ≠ z ∧ tau a b c δ f k y ≠ x ∧
    tau a b c δ f k y ≠ z ∧ tau a b c δ f k z ≠ x ∧ tau a b c δ f k z ≠ y

/-- The family `f` is bad for the pair `(u, v)`. -/
def famBad (a b c : ℕ) (f : ℕ) (u v : Fin (a + b + c)) : Prop :=
  col3 a b c u = col3 a b c v ∧
    (u.val + mdl a b c (col3 a b c u) f = v.val ∨ v.val + mdl a b c (col3 a b c u) f = u.val)

theorem famBad_unique (h : BigCls a b c) {f f' : ℕ} (hf : f < 4) (hf' : f' < 4)
    {u v : Fin (a + b + c)} (h1 : famBad a b c f u v) (h2 : famBad a b c f' u v) : f = f' := by
  obtain ⟨-, d1⟩ := h1
  obtain ⟨-, d2⟩ := h2
  have hl := clen_ge h (col3 a b c u)
  unfold mdl at d1 d2
  omega

theorem exists_good_fam (h : BigCls a b c) (x y z : Fin (a + b + c)) :
    ∃ f < 4, ¬ famBad a b c f x y ∧ ¬ famBad a b c f x z ∧ ¬ famBad a b c f y z := by
  by_contra hno
  push_neg at hno
  -- every family is bad for one of the three pairs: pigeonhole
  have key : ∀ f : Fin 4, ∃ p : Fin 3, (p = 0 ∧ famBad a b c f x y) ∨
      (p = 1 ∧ famBad a b c f x z) ∨ (p = 2 ∧ famBad a b c f y z) := by
    intro f
    by_cases h1 : famBad a b c f x y
    · exact ⟨0, Or.inl ⟨rfl, h1⟩⟩
    by_cases h2 : famBad a b c f x z
    · exact ⟨1, Or.inr (Or.inl ⟨rfl, h2⟩)⟩
    exact ⟨2, Or.inr (Or.inr ⟨rfl, hno f f.isLt h1 h2⟩)⟩
  choose g hg using key
  obtain ⟨f, -, f', -, hne, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (univ : Finset (Fin 4))) (t := (univ : Finset (Fin 3))) (by simp) (f := g)
    (fun _ _ => mem_univ _)
  apply hne
  have H := hg f
  have H' := hg f'
  rw [he] at H
  ext
  rcases H with ⟨e, b1⟩ | ⟨e, b1⟩ | ⟨e, b1⟩ <;> rcases H' with ⟨e', b2⟩ | ⟨e', b2⟩ | ⟨e', b2⟩ <;>
    first
    | exact famBad_unique h f.isLt f'.isLt b1 b2
    | (rw [e] at e'; exact absurd e' (by decide))

theorem exists_good_shift (h : BigCls a b c) {δ : ℕ} (hδ : δ < 6) (hδ0 : 0 < δ)
    {x y z : Fin (a + b + c)} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ f < 4, ∃ k < 7, GoodShift a b c δ f k x y z := by
  obtain ⟨f, hf, bxy, bxz, byz⟩ := exists_good_fam h x y z
  -- injectivity on the triangle, for every `k`
  have inj : ∀ k < 7, ∀ {u v : Fin (a + b + c)}, u ≠ v → ¬ famBad a b c f u v →
      tau a b c δ f k u ≠ tau a b c δ f k v := by
    intro k hk u v huv hb he
    rcases tau_eq h hδ hf hk he with e | hb'
    · exact huv e
    · exact hb hb'
  -- the `k` hitting a given ordered pair is unique
  have hit : ∀ {u v : Fin (a + b + c)} {k k' : ℕ}, k < 7 → k' < 7 → tau a b c δ f k u = v →
      tau a b c δ f k' u = v → k = k' :=
    fun hk hk' e e' => tau_inj_k h hδ hf hk hk' _ (e.trans e'.symm)
  by_contra hno
  push_neg at hno
  have key : ∀ k : Fin 7, ∃ p : Fin 6,
      (p = 0 ∧ tau a b c δ f k x = y) ∨ (p = 1 ∧ tau a b c δ f k x = z) ∨
      (p = 2 ∧ tau a b c δ f k y = x) ∨ (p = 3 ∧ tau a b c δ f k y = z) ∨
      (p = 4 ∧ tau a b c δ f k z = x) ∨ (p = 5 ∧ tau a b c δ f k z = y) := by
    intro k
    have hk := k.isLt
    have hn := hno f hf k hk
    unfold GoodShift at hn
    have i1 := inj k hk hxy bxy
    have i2 := inj k hk hxz bxz
    have i3 := inj k hk hyz byz
    by_cases c0 : tau a b c δ f k x = y
    · exact ⟨0, Or.inl ⟨rfl, c0⟩⟩
    by_cases c1 : tau a b c δ f k x = z
    · exact ⟨1, Or.inr (Or.inl ⟨rfl, c1⟩)⟩
    by_cases c2 : tau a b c δ f k y = x
    · exact ⟨2, Or.inr (Or.inr (Or.inl ⟨rfl, c2⟩))⟩
    by_cases c3 : tau a b c δ f k y = z
    · exact ⟨3, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, c3⟩)))⟩
    by_cases c4 : tau a b c δ f k z = x
    · exact ⟨4, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, c4⟩))))⟩
    by_cases c5 : tau a b c δ f k z = y
    · exact ⟨5, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, c5⟩))))⟩
    exact (hn ⟨i1, i2, i3, c0, c1, c2, c3, c4, c5⟩).elim
  choose g hg using key
  obtain ⟨k, -, k', -, hne, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (univ : Finset (Fin 7))) (t := (univ : Finset (Fin 6))) (by simp) (f := g)
    (fun _ _ => mem_univ _)
  apply hne
  have H := hg k
  have H' := hg k'
  rw [he] at H
  ext
  rcases H with ⟨e, b1⟩ | ⟨e, b1⟩ | ⟨e, b1⟩ | ⟨e, b1⟩ | ⟨e, b1⟩ | ⟨e, b1⟩ <;>
  rcases H' with ⟨e', b2⟩ | ⟨e', b2⟩ | ⟨e', b2⟩ | ⟨e', b2⟩ | ⟨e', b2⟩ | ⟨e', b2⟩ <;>
    first
    | exact hit k.isLt k'.isLt b1 b2
    | (rw [e] at e'; exact absurd e' (by decide))

end CDRBicolour.Absorption.Refined
