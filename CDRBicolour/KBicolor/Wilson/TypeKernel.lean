/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.OptimalWeights

/-!
# The reference type kernel and a sharper complete-host seed constant

`classKernel` is the third-colour kernel of the type-uniform seed, with zero
weight on forbidden triples. Its reference edge mass is exactly one after the
two root contributions are removed. Allowed weights lie in [η/n,2/(δn)].
Consequently the complete-host diffuse constant can be max(1/η,2/δ), replacing
the older sum 1/η+2/δ without changing the hypotheses or the edge equations.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle
open scoped Classical

variable {k : ℕ}

def classKernel (c : Fin k → ℕ) (a : Fin k → Fin k → ℝ) (i j l : Fin k) : ℝ :=
  if i = j then (if l = i then 0 else a i l / ((c i : ℝ) - 1))
  else if l = i then a i j / ((c i : ℝ) - 1)
  else if l = j then a j i / ((c j : ℝ) - 1) else 0

theorem classKernel_eq (c : Fin k → ℕ) (a : Fin k → Fin k → ℝ) (i j l : Fin k) :
    (if ({i, j, l} : Multiset (Fin k)) ∈ bicF k then seedW c a {i, j, l} else 0) =
      classKernel c a i j l := by
  by_cases hij : i = j
  · subst hij
    by_cases hli : l = i
    · subst hli
      have hnot : ({l, l, l} : Multiset (Fin k)) ∉ bicF k := by rw [mem_bicF]; simp
      rw [ite_eq_right hnot]
      simp [classKernel]
    · simp only [classKernel, ite_true, eq_self_iff_true, ite_eq_right hli]
      rw [if_pos (mem_bicF.mpr (Or.inl ⟨rfl, (Ne.symm hli)⟩)), seedW_xxy c a (Ne.symm hli)]
  · by_cases hli : l = i
    · subst hli
      rw [if_pos (mem_bicF.mpr (Or.inr (Or.inl ⟨rfl, hij⟩))), perm_aba,
        seedW_xxy c a hij]
      simp [classKernel, hij]
    · by_cases hlj : l = j
      · subst hlj
        rw [if_pos (mem_bicF.mpr (Or.inr (Or.inr ⟨rfl, hij⟩))), perm_abb,
          seedW_xxy c a (Ne.symm hij)]
        simp [classKernel, hij, (Ne.symm hij)]
      · have hnot : ({i, j, l} : Multiset (Fin k)) ∉ bicF k := by
          simp only [mem_bicF]
          tauto
        rw [ite_eq_right hnot]
        simp [classKernel, hij, hli, hlj]

/-- Reference edge mass, including the exact two root exclusions. -/
theorem classKernel_mass (c : Fin k → ℕ) (a : Fin k → Fin k → ℝ) {η : ℝ}
    (hs : SeedData c η a) (hc : ∀ i, 1 < (c i : ℝ)) (i j : Fin k) :
    (∑ l, (c l : ℝ) * classKernel c a i j l) -
      classKernel c a i j i - classKernel c a i j j = 1 := by
  by_cases hij : i = j
  · subst hij
    simp only [classKernel, eq_self_iff_true, ite_true, sub_zero]
    have he : (∑ l, (c l : ℝ) * (if l = i then 0 else a i l / ((c i : ℝ) - 1))) =
        (∑ l ∈ univ.filter (fun l => l ≠ i), (c l : ℝ) * a i l) / ((c i : ℝ) - 1) := by
      rw [sum_div, sum_filter]
      apply sum_congr rfl
      intro l _
      by_cases hl : l = i <;> simp [hl, mul_div_assoc]
    rw [he, hs.2.2 i]
    exact div_self (by linarith [hc i])
  · have he : (∑ l, (c l : ℝ) * classKernel c a i j l) =
        (c i : ℝ) * (a i j / ((c i : ℝ) - 1)) +
          (c j : ℝ) * (a j i / ((c j : ℝ) - 1)) := by
      have hpoint : ∀ l, (c l : ℝ) * classKernel c a i j l =
          (if l = i then (c i : ℝ) * (a i j / ((c i : ℝ) - 1)) else 0) +
          (if l = j then (c j : ℝ) * (a j i / ((c j : ℝ) - 1)) else 0) := by
        intro l
        by_cases hli : l = i <;> by_cases hlj : l = j <;>
          simp_all [classKernel]
      simp_rw [hpoint]
      simp only [sum_add_distrib, sum_ite_eq', mem_univ, if_true]
    rw [he]
    simp [classKernel, hij, Ne.symm hij]
    calc
      _ = ((c i : ℝ) - 1) * (a i j / ((c i : ℝ) - 1)) +
          ((c j : ℝ) - 1) * (a j i / ((c j : ℝ) - 1)) := by ring
      _ = a i j + a j i := by field_simp [show (c i : ℝ) - 1 ≠ 0 by linarith [hc i],
        show (c j : ℝ) - 1 ≠ 0 by linarith [hc j]]
      _ = 1 := hs.1 i j hij

theorem seedW_sharp_bounds (c : Fin k → ℕ) (a : Fin k → Fin k → ℝ) {η δ n : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n) (hs : SeedData c η a)
    (hcls : ∀ i, δ * n ≤ c i) (hsize : ∀ i, (c i : ℝ) ≤ n) (h2 : 2 ≤ δ * n)
    {m : Multiset (Fin k)} (hm : m ∈ bicF k) :
    η / n ≤ seedW c a m ∧ seedW c a m ≤ 2 / (δ * n) := by
  obtain ⟨i, j, hij, rfl⟩ := bicF_cases hm
  rw [seedW_xxy c a hij]
  have hpos : 0 < (c i : ℝ) - 1 := by linarith [hcls i]
  have ha := hs.2.1 i j hij
  have hb : a i j ≤ 1 := by
    have hsum := hs.1 i j hij
    have hlow := hs.2.1 j i (Ne.symm hij)
    linarith
  constructor
  · apply (div_le_div_iff₀ hn hpos).mpr
    calc
      η * ((c i : ℝ) - 1) ≤ η * n := mul_le_mul_of_nonneg_left (by linarith [hsize i]) hη.le
      _ ≤ a i j * n := mul_le_mul_of_nonneg_right ha hn.le
  · apply (div_le_div_iff₀ hpos (mul_pos hδ hn)).mpr
    nlinarith [hcls i, mul_le_mul_of_nonneg_right hb (mul_nonneg hδ.le hn.le)]

/-- A sharper diffuse constant for exactly the same type-uniform complete-host seed. -/
theorem kH1_max {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin k) {η δ : ℝ}
    {a : Fin k → Fin k → ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hs : SeedData (ksz lab) η a) (hcls : ∀ i, δ * Fintype.card V ≤ ksz lab i)
    (h2 : 2 ≤ δ * Fintype.card V) :
    IsDiffuseSeed (kHost lab) (bicF k) (max (1 / η) (2 / δ))
      (fun T => seedW (ksz lab) a (T.val.map lab)) := by
  have hn : (0 : ℝ) < Fintype.card V := by
    have hp : 0 < δ * Fintype.card V := by linarith
    exact pos_of_mul_pos_right hp hδ.le
  have hsize : ∀ i, (ksz lab i : ℝ) ≤ Fintype.card V := by
    intro i
    exact_mod_cast (card_le_univ (univ.filter fun v => lab v = i))
  have hCpos : 0 < max (1 / η) (2 / δ) := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨fun T hT => ?_, (kH1 lab hη hδ hs hcls h2).2⟩
  obtain ⟨hl, hu⟩ := seedW_sharp_bounds (ksz lab) a hη hδ hn hs hcls hsize h2 hT.2.2
  constructor
  · calc
      _ ≤ 1 / ((1 / η) * Fintype.card V) :=
        one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right (le_max_left _ _) hn.le)
      _ = η / Fintype.card V := by field_simp
      _ ≤ _ := hl
  · calc
      _ ≤ 2 / (δ * Fintype.card V) := hu
      _ = (2 / δ) / Fintype.card V := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hn.le

end CDRBicolour.KBicolor.Wilson
