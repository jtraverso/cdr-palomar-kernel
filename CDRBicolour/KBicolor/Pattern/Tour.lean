/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Pattern.Outline
public import CDRBicolour.PaperIII.Defs

/-!
# Integer tournaments from Gale's feasibility theorem

For class sizes `m` on the cone `3 Σ m² = (Σ m)²`, a tournament (`IsTour m x`) exists as soon as
every set `S` of classes satisfies the cut condition `cutZ S m ≤ 0`:

    Σ_{P∈S} m_P² ≤ Σ_{P<Q in S} m_P m_Q + Σ_{P∈S, Q∉S} m_P m_Q.

This is Gale's integer feasibility theorem (`GaleInt`, discharged from Palomar 000015) applied to
the antisymmetric flow `f = x − x₀`, with `x₀` the upper-triangular split.
-/

@[expose] public section

namespace CDRBicolour.KBicolor.Pattern

open Finset

variable {k : ℕ}

/-- The upper-triangular split. -/
def x0 (m : Fin k → ℕ) (P Q : Fin k) : ℕ := if P < Q then m P * m Q else 0

/-- The cut functional (integer form). -/
def cutZ (S : Finset (Fin k)) (m : Fin k → ℕ) : ℤ :=
  ∑ P ∈ S, (m P : ℤ) ^ 2 - ∑ P ∈ S, ∑ Q ∈ S, (x0 m P Q : ℤ) -
    ∑ P ∈ S, ∑ Q ∈ Sᶜ, (m P : ℤ) * m Q

theorem x0_add (m : Fin k → ℕ) {P Q : Fin k} (h : P ≠ Q) : x0 m P Q + x0 m Q P = m P * m Q := by
  unfold x0
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [h', not_lt.2 h'.le]
  · simp [h', not_lt.2 h'.le, mul_comm]

theorem x0_self (m : Fin k → ℕ) (P : Fin k) : x0 m P P = 0 := by simp [x0]

theorem mul_eq_x0 (m : Fin k → ℕ) (P Q : Fin k) :
    (m P : ℤ) * m Q = x0 m P Q + x0 m Q P + (if P = Q then (m P : ℤ) * m P else 0) := by
  by_cases h : P = Q
  · subst h; simp [x0_self]
  · simp only [h, if_false, add_zero]; exact_mod_cast (x0_add m h).symm

/-- `(Σ m)² = Σ m² + 2 Σ x₀`. -/
theorem sq_sum_eq (m : Fin k → ℕ) :
    (∑ P, (m P : ℤ)) ^ 2 = ∑ P, (m P : ℤ) ^ 2 + 2 * ∑ P, ∑ Q, (x0 m P Q : ℤ) := by
  rw [sq, Finset.sum_mul_sum,
    Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => mul_eq_x0 m P Q]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun P Q => (x0 m Q P : ℤ))]
  ring

theorem cutZ_univ (m : Fin k → ℕ)
    (hcone : 3 * ∑ P, m P ^ 2 = (∑ P, m P) ^ 2) : cutZ univ m = 0 := by
  have h1 := sq_sum_eq m
  have h2 : (3 * ∑ P, (m P : ℤ) ^ 2) = (∑ P, (m P : ℤ)) ^ 2 := by exact_mod_cast hcone
  unfold cutZ
  simp only [Finset.compl_univ, Finset.sum_empty, Finset.sum_const_zero, sub_zero]
  linarith

/-- **Tournaments from cut conditions.** -/
theorem exists_tour (hG : PaperIII.GaleInt) (m : Fin k → ℕ)
    (hcone : 3 * ∑ P, m P ^ 2 = (∑ P, m P) ^ 2) (hcut : ∀ S, cutZ S m ≤ 0) :
    ∃ x, IsTour m x := by
  classical
  set c : Fin k → Fin k → ℤ := fun P Q => (x0 m Q P : ℤ) with hc
  set d : Fin k → ℤ := fun P => (m P : ℤ) ^ 2 - ∑ Q, (x0 m P Q : ℤ) with hd
  have hc0 : ∀ P Q, 0 ≤ c P Q := fun _ _ => Nat.cast_nonneg _
  have hdsum : ∑ P, d P = 0 := by
    have := cutZ_univ m hcone
    unfold cutZ at this
    simp only [Finset.compl_univ, Finset.sum_empty, Finset.sum_const_zero, sub_zero] at this
    rw [hd]; simp only [Finset.sum_sub_distrib]; linarith
  have hgale : ∀ S : Finset (Fin k), ∑ P ∈ S, d P ≤ ∑ P ∈ S, ∑ Q ∈ Sᶜ, c P Q := by
    intro S
    have hS := hcut S
    unfold cutZ at hS
    have split : ∀ P, ∑ Q, (x0 m P Q : ℤ) = ∑ Q ∈ S, (x0 m P Q : ℤ) + ∑ Q ∈ Sᶜ, (x0 m P Q : ℤ) :=
      fun P => (Finset.sum_add_sum_compl S _).symm
    have hcross : ∀ P ∈ S, ∑ Q ∈ Sᶜ, (m P : ℤ) * m Q =
        ∑ Q ∈ Sᶜ, (x0 m P Q : ℤ) + ∑ Q ∈ Sᶜ, (x0 m Q P : ℤ) := by
      intro P hP
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have hne : P ≠ Q := by
        rintro rfl; exact (Finset.mem_compl.1 hQ) hP
      exact_mod_cast (x0_add m hne).symm
    rw [Finset.sum_congr rfl hcross, Finset.sum_add_distrib] at hS
    simp only [hd, hc, Finset.sum_sub_distrib, split, Finset.sum_add_distrib]
    linarith
  obtain ⟨f, hanti, hle, hsum⟩ := (hG (Fin k) c hc0 d hdsum).2 hgale
  set x : Fin k → Fin k → ℤ := fun P Q => (x0 m P Q : ℤ) + f P Q with hx
  have hx0 : ∀ P Q, 0 ≤ x P Q := by
    intro P Q
    have h1 := hle Q P
    have h2 := hanti P Q
    simp only [hx, hc] at h1 ⊢
    linarith
  have hff : ∀ P, f P P = 0 := fun P => by have := hanti P P; linarith
  refine ⟨fun P Q => (x P Q).toNat, ⟨fun P => ?_, fun P Q hPQ => ?_, fun P => ?_⟩⟩
  · simp [hx, x0_self, hff]
  · have e : (((x P Q).toNat + (x Q P).toNat : ℕ) : ℤ) = ((m P * m Q : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg (hx0 P Q), Int.toNat_of_nonneg (hx0 Q P)]
      simp only [hx]
      have := hanti P Q
      have h3 : ((x0 m P Q + x0 m Q P : ℕ) : ℤ) = ((m P * m Q : ℕ) : ℤ) := by
        rw [x0_add m hPQ]
      push_cast at h3
      linarith
    exact_mod_cast e
  · have e : ((∑ Q, (x P Q).toNat : ℕ) : ℤ) = ((m P * m P : ℕ) : ℤ) := by
      push_cast
      rw [Finset.sum_congr rfl fun Q _ => Int.toNat_of_nonneg (hx0 P Q)]
      simp only [hx, Finset.sum_add_distrib, hsum P, hd]
      ring
    exact_mod_cast e

end CDRBicolour.KBicolor.Pattern
