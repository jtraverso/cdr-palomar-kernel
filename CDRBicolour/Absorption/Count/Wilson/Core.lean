/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Count.Wilson.Assembly
public import CountingCone.Construction

/-!
# Optimal counting constant, part 9: the core bound (item 4)

`wilson_core`: for an admissible profile, `g ≥ 15` admissible, `t = ⌊2 min(a,b,c)/(2g+1)⌋` and the
conclusion of Theorem T for the constants `α = 1/(16(2g+1))²`, `C = 6g(2g+1) + 8`, under explicit
largeness conditions,

    (3/2) g (g − 1) t² (log t − 2) ≤ log realCount(a, b, c).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Count.Wilson

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Count

/-- A Steiner triple system on `Fin g`. -/
theorem exists_sts {g : ℕ} (hg : 15 ≤ g) (ha : _root_.STS.Admissible g) :
    ∃ S : Finset (Finset (Fin g)), _root_.STS.IsSTS S := by
  have h1 := _root_.STS.lemma4 g hg ha
  unfold _root_.STS.D7 at h1
  obtain ⟨⟨B, hB, -⟩⟩ := (Nat.card_pos_iff.1 (lt_of_lt_of_le Nat.zero_lt_one h1)).1
  exact ⟨B, hB⟩

/-- The cyclic Latin square. -/
theorem cyc_latin {t : ℕ} (ht : 0 < t) :
    _root_.STS.IsLatin (fun i j : Fin t => (⟨(i.val + j.val) % t, Nat.mod_lt _ ht⟩ : Fin t)) := by
  refine ⟨fun i => ?_, fun j => ?_⟩
  · rw [← Finite.injective_iff_bijective]
    intro j j' he
    simp only [Fin.mk.injEq] at he
    have := Nat.ModEq.add_left_cancel' i.val he
    exact Fin.ext (by
      unfold Nat.ModEq at this; rwa [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at this)
  · rw [← Finite.injective_iff_bijective]
    intro i i' he
    simp only [Fin.mk.injEq] at he
    have := Nat.ModEq.add_right_cancel' j.val he
    exact Fin.ext (by
      unfold Nat.ModEq at this; rwa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt i'.isLt] at this)

/-- Pairwise differences of an admissible profile. -/
theorem adm_diff {a b c : ℕ} (h : AdmissibleProfile a b c) :
    ((a : ℝ) - b) ^ 2 + ((a : ℝ) - c) ^ 2 + ((b : ℝ) - c) ^ 2 = 2 * (a + b + c) := by
  have e := h.2.2.2.2.1
  have e' : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 - a * b - a * c - b * c = a + b + c := by
    exact_mod_cast e
  linear_combination 2 * e'

theorem csize_ge_min {a b c : ℕ} (P : Fin 3) : min a (min b c) ≤ csize a b c P := by
  unfold csize; split_ifs <;> omega

theorem csize_diff {a b c : ℕ} (h : AdmissibleProfile a b c) (P Q : Fin 3) :
    |(csize a b c P : ℝ) - csize a b c Q| ≤ Real.sqrt (2 * (a + b + c : ℕ)) := by
  apply Real.abs_le_sqrt
  have e := adm_diff h
  push_cast
  have s1 := sq_nonneg ((a : ℝ) - b); have s2 := sq_nonneg ((a : ℝ) - c)
  have s3 := sq_nonneg ((b : ℝ) - c)
  fin_cases P <;> fin_cases Q <;> simp [csize] <;> nlinarith

theorem csize_le_min_add {a b c : ℕ} (h : AdmissibleProfile a b c) (P : Fin 3) :
    (csize a b c P : ℝ) ≤ min a (min b c) + Real.sqrt (2 * (a + b + c : ℕ)) := by
  have hm : ∃ Q, csize a b c Q = min a (min b c) := by
    by_cases h1 : a ≤ b ∧ a ≤ c
    · exact ⟨0, by simp [csize]; omega⟩
    · by_cases h2 : b ≤ c
      · exact ⟨1, by simp [csize]; omega⟩
      · exact ⟨2, by simp [csize]; omega⟩
  obtain ⟨Q, hQ⟩ := hm
  have := abs_le.1 (csize_diff h P Q)
  rw [hQ] at this
  push_cast at this ⊢
  linarith [this.2]

end CDRBicolour.Absorption.Count.Wilson
