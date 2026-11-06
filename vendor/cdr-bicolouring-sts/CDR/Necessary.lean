/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDR.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Necessary conditions for bicolourings (Dinitz–Stinson, Proposition 1.2)

* `not_two_classes_of_size_two` (**duplicity**, Proposition 1.2 (2)): no bicolouring of an STS
  has two distinct colour classes of size `2`. In particular there is no `(2, 2, 5)`-bicolouring
  of an STS(`9`).
* `Bicolourable3.not_two_odd` (**oddity**, Proposition 1.2 (3), for three colour classes): at
  most one of `a, b, c` is odd. The argument of the papers (the number of two-coloured pairs is
  even) gives `ab + bc + ca` even, which excludes two or three odd classes when there are three
  classes.
-/

@[expose] public section

namespace CDR

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The third point of a block through two given points. -/
theorem IsSTS.exists_third {B : Finset (Finset X)} (hB : IsSTS B) {t : Finset X} (ht : t ∈ B)
    {a b : X} (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b) :
    ∃ w, w ≠ a ∧ w ≠ b ∧ t = {a, b, w} := by
  have h3 := hB.card_eq t ht
  have hsub : ({a, b} : Finset X) ⊆ t := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard : #(t \ {a, b}) = 1 := by
    rw [card_sdiff_of_subset hsub, h3, card_pair hab]
  obtain ⟨w, hw⟩ := card_eq_one.1 hcard
  have hwt : w ∈ t \ {a, b} := by rw [hw]; exact mem_singleton_self w
  simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hwt
  refine ⟨w, hwt.2.1, hwt.2.2, ?_⟩
  have : t = {a, b} ∪ (t \ {a, b}) := (union_sdiff_of_subset hsub).symm
  rw [this, hw]
  ext x
  simp [or_assoc]

/-- In a bicoloured block through two points of different colours, the third point has one of
these two colours. -/
theorem colour_third {κ : Type*} [DecidableEq κ] {B : Finset (Finset X)} {φ : X → κ}
    (hφ : IsBicolouring B φ) {a b w : X} (ht : ({a, b, w} : Finset X) ∈ B) (hab : φ a ≠ φ b) :
    φ w = φ a ∨ φ w = φ b := by
  have h2 := hφ _ ht
  rw [image_insert, image_insert, image_singleton] at h2
  by_contra hno
  push Not at hno
  rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton] at h2
  · omega
  · simp only [mem_singleton]
    exact fun h => hno.2 h.symm
  · simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hab, fun h => hno.1 h.symm⟩

/-- **Duplicity (Dinitz–Stinson, Proposition 1.2 (2)).** A bicolouring of an STS has no two
distinct colour classes of size `2`. -/
theorem not_two_classes_of_size_two {κ : Type*} [DecidableEq κ] {B : Finset (Finset X)}
    {φ : X → κ} (hB : IsSTS B) (hφ : IsBicolouring B φ) {k l : κ} (hkl : k ≠ l)
    (hk : #(univ.filter fun x => φ x = k) = 2) (hl : #(univ.filter fun x => φ x = l) = 2) :
    False := by
  obtain ⟨x₁, x₂, hx, hxk⟩ := card_eq_two.1 hk
  obtain ⟨y₁, y₂, hy, hyl⟩ := card_eq_two.1 hl
  have mx : ∀ z, φ z = k ↔ z = x₁ ∨ z = x₂ := fun z => by
    have := congrArg (z ∈ ·) hxk
    simpa using this
  have my : ∀ z, φ z = l ↔ z = y₁ ∨ z = y₂ := fun z => by
    have := congrArg (z ∈ ·) hyl
    simpa using this
  have hx₁ := (mx x₁).2 (Or.inl rfl)
  have hx₂ := (mx x₂).2 (Or.inr rfl)
  have hy₁ := (my y₁).2 (Or.inl rfl)
  have hy₂ := (my y₂).2 (Or.inr rfl)
  have hne : ∀ {a b}, φ a = k → φ b = l → a ≠ b := fun ha hb h => hkl (ha.symm.trans (h ▸ hb))
  -- the block through `a` (colour `k`) and `b` (colour `l`) has its third point in `k ∪ l`
  have third : ∀ {a b}, φ a = k → φ b = l → ∃ t ∈ B, ∃ w, t = {a, b, w} ∧
      (w = x₁ ∨ w = x₂ ∨ w = y₁ ∨ w = y₂) ∧ w ≠ a ∧ w ≠ b := by
    intro a b ha hb
    obtain ⟨t, ⟨ht, hat, hbt⟩, -⟩ := hB.pair a b (hne ha hb)
    obtain ⟨w, hwa, hwb, rfl⟩ := hB.exists_third ht hat hbt (hne ha hb)
    refine ⟨_, ht, w, rfl, ?_, hwa, hwb⟩
    rcases colour_third hφ ht (by rw [ha, hb]; exact hkl) with h | h
    · rcases (mx w).1 (h.trans ha) with h' | h' <;> simp [h']
    · rcases (my w).1 (h.trans hb) with h' | h' <;> simp [h']
  have uniq : ∀ {t t' : Finset X} {a b}, t ∈ B → t' ∈ B → a ≠ b → a ∈ t → b ∈ t → a ∈ t' →
      b ∈ t' → t = t' := fun ht ht' hab ha hb ha' hb' => by
    obtain ⟨s, -, hs⟩ := hB.pair _ _ hab
    exact (hs _ ⟨ht, ha, hb⟩).trans (hs _ ⟨ht', ha', hb'⟩).symm
  obtain ⟨t, ht, w, rfl, hw, hwa, hwb⟩ := third hx₁ hy₁
  rcases hw with hw | hw | hw | hw <;> subst w
  · exact hwa rfl
  · -- `t = {x₁, y₁, x₂}`; the block through `x₁, y₂`
    obtain ⟨t', ht', w', rfl, hw', hw'a, hw'b⟩ := third hx₁ hy₂
    rcases hw' with hw' | hw' | hw' | hw' <;> subst w'
    · exact hw'a rfl
    · have := uniq ht ht' hx (by simp) (by simp) (by simp) (by simp)
      have hmem : y₂ ∈ ({x₁, y₁, x₂} : Finset X) := this ▸ (by simp)
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact hne hx₁ hy₂ h.symm
      · exact hy (h.symm)
      · exact hne hx₂ hy₂ h.symm
    · have := uniq ht ht' (hne hx₁ hy₁) (by simp) (by simp) (by simp) (by simp)
      have hmem : y₂ ∈ ({x₁, y₁, x₂} : Finset X) := this ▸ (by simp)
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact hne hx₁ hy₂ h.symm
      · exact hy (h.symm)
      · exact hne hx₂ hy₂ h.symm
    · exact hw'b rfl
  · exact hwb rfl
  · -- `t = {x₁, y₁, y₂}`; the block through `x₂, y₁`
    obtain ⟨t', ht', w', rfl, hw', hw'a, hw'b⟩ := third hx₂ hy₁
    rcases hw' with hw' | hw' | hw' | hw' <;> subst w'
    · have := uniq ht ht' (hne hx₁ hy₁) (by simp) (by simp) (by simp) (by simp)
      have hmem : x₂ ∈ ({x₁, y₁, y₂} : Finset X) := this ▸ (by simp)
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact hx h.symm
      · exact hne hx₂ hy₁ h
      · exact hne hx₂ hy₂ h
    · exact hw'a rfl
    · exact hw'b rfl
    · have := uniq ht ht' hy (by simp) (by simp) (by simp) (by simp)
      have hmem : x₂ ∈ ({x₁, y₁, y₂} : Finset X) := this ▸ (by simp)
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact hx h.symm
      · exact hne hx₂ hy₁ h
      · exact hne hx₂ hy₂ h

/-- In particular, no STS(`9`) has a `(2, 2, 5)`-bicolouring. -/
theorem not_bicolourable3_two_two (v c : ℕ) : ¬ Bicolourable3 v 2 2 c := by
  rintro ⟨B, φ, hB, hφ, ha, hb, -⟩
  exact not_two_classes_of_size_two hB hφ (k := 0) (l := 1) (by decide) ha hb

/-- `ab + bc + ca = 2|B|` for a bicoloured STS with three colour classes. -/
theorem Bicolourable3.two_mul_card_eq {v a b c : ℕ} {B : Finset (Finset (Fin v))}
    {φ : Fin v → Fin 3} (hB : IsSTS B) (hφ : IsBicolouring B φ) (ha : #(colourClass φ 0) = a)
    (hb : #(colourClass φ 1) = b) (hc : #(colourClass φ 2) = c) :
    a * b + b * c + c * a = 2 * #B := by
  have h6 := hB.six_mul_card
  have h2 := hB.two_mul_card hφ
  rw [Fin.sum_univ_three, ha, hb, hc] at h2
  have hv : Fintype.card (Fin v) = a + b + c := by
    rw [← ha, ← hb, ← hc]
    simp only [colourClass]
    rw [← card_univ, card_eq_sum_card_fiberwise (f := φ) (t := univ) (fun _ _ => mem_univ _),
      Fin.sum_univ_three]
  rw [hv] at h6
  have e : ∀ n : ℕ, n * (n - 1) = n * n - n := fun n => Nat.mul_sub_one n n
  rw [e, e, e] at h2
  rw [e] at h6
  have l1 : ∀ n : ℕ, n ≤ n * n := fun n => Nat.le_mul_self n
  have := l1 a
  have := l1 b
  have := l1 c
  have := l1 (a + b + c)
  zify [l1 a, l1 b, l1 c, l1 (a + b + c)] at h2 h6 ⊢
  nlinarith

/-- **Oddity (Dinitz–Stinson, Proposition 1.2 (3), three classes).** In a `3`-bicoloured STS,
at most one of the class sizes is odd. -/
theorem Bicolourable3.not_two_odd {v a b c : ℕ} (h : Bicolourable3 v a b c) :
    ¬ (Odd a ∧ Odd b) ∧ ¬ (Odd b ∧ Odd c) ∧ ¬ (Odd c ∧ Odd a) := by
  obtain ⟨B, φ, hB, hφ, ha, hb, hc⟩ := h
  have key := Bicolourable3.two_mul_card_eq hB hφ ha hb hc
  have odd_sum : ∀ x y z : ℕ, Odd x → Odd y → x * y + y * z + z * x ≠ 2 * #B := by
    rintro x y z ⟨i, rfl⟩ ⟨j, rfl⟩ h
    have : (2 * i + 1) * (2 * j + 1) + (2 * j + 1) * z + z * (2 * i + 1) =
        2 * (2 * i * j + i + j + j * z + z * i + z) + 1 := by ring
    omega
  refine ⟨fun ⟨hoa, hob⟩ => odd_sum a b c hoa hob key, fun ⟨hob, hoc⟩ => ?_,
    fun ⟨hoc, hoa⟩ => ?_⟩
  · exact odd_sum b c a hob hoc (by rw [← key]; ring)
  · exact odd_sum c a b hoc hoa (by rw [← key]; ring)

end CDR
