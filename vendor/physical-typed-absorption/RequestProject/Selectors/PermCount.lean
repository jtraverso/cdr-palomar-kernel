/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Counting permutations that map a set into a set

For a finite type `α` with `n` elements, finsets `Y, T ⊆ α`, `|Y| = a`, `|T| = t`:

  `#{π : Perm α | π '' Y ⊆ T} * n ^ a ≤ n! * t ^ a`,

i.e. a uniform permutation maps `Y` into `T` with probability `≤ (t/n)^a`
(sampling without replacement).  Proof: the count only depends on `|Y|` (translate by a
permutation), the sum over all `a`-sets equals `n! * C(t,a)` (double counting), and
`C(t,a) n^a ≤ C(n,a) t^a`.
-/

namespace SelCount

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Number of permutations mapping `Y` into `T`. -/
def permInto (Y T : Finset α) : ℕ :=
  (univ.filter (fun π : Equiv.Perm α => ∀ y ∈ Y, π y ∈ T)).card

lemma permInto_map (σ : Equiv.Perm α) (Y T : Finset α) :
    permInto (Y.map σ.toEmbedding) T = permInto Y T := by
  unfold permInto
  refine Finset.card_bij (fun π _ => π * σ) ?_ ?_ ?_
  · intro π hπ
    simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hπ ⊢
    intro y hy; exact hπ y hy
  · intro π₁ _ π₂ _ h; exact mul_right_cancel h
  · intro π hπ
    refine ⟨π * σ⁻¹, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hπ ⊢
    intro y hy; simpa using hπ y hy

lemma exists_perm_map_eq (Y Y' : Finset α) (h : Y.card = Y'.card) :
    ∃ σ : Equiv.Perm α, Y.map σ.toEmbedding = Y' := by
  have e : Y ≃ Y' := Fintype.equivOfCardEq (by simpa using h)
  let f : α → α := fun x => if hx : x ∈ Y then (e ⟨x, hx⟩ : α) else x
  have hinj : Set.InjOn f ↑Y := by
    intro x hx y hy hxy
    simp only [f, dif_pos (show x ∈ Y from hx), dif_pos (show y ∈ Y from hy)] at hxy
    have := e.injective (Subtype.ext hxy)
    simpa using this
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq (t := (univ : Finset α))
    (by simp) (s := Y) (f := f) (subset_univ _) hinj
  let σ : Equiv.Perm α := g.trans (Equiv.subtypeUnivEquiv (fun x => mem_univ x))
  refine ⟨σ, ?_⟩
  have hσ : ∀ x ∈ Y, σ x = f x := fun x hx => by
    simp [σ, Equiv.subtypeUnivEquiv, hg x hx]
  ext z
  simp only [mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hσ x hx]; simp [f, hx]
  · intro hz
    refine ⟨(e.symm ⟨z, hz⟩ : α), (e.symm ⟨z, hz⟩).2, ?_⟩
    rw [hσ _ (e.symm ⟨z, hz⟩).2]
    simp [f]

lemma permInto_eq_of_card (Y Y' T : Finset α) (h : Y.card = Y'.card) :
    permInto Y T = permInto Y' T := by
  obtain ⟨σ, rfl⟩ := exists_perm_map_eq Y Y' h
  exact (permInto_map σ Y T).symm

lemma sum_permInto (a : ℕ) (T : Finset α) :
    ∑ Y ∈ powersetCard a (univ : Finset α), permInto Y T =
      (Fintype.card α).factorial * T.card.choose a := by
  unfold permInto
  simp_rw [card_filter]
  rw [Finset.sum_comm]
  have key : ∀ π : Equiv.Perm α,
      (∑ Y ∈ powersetCard a (univ : Finset α), if ∀ y ∈ Y, π y ∈ T then 1 else 0) =
        T.card.choose a := by
    intro π
    rw [← card_filter]
    have : (powersetCard a (univ : Finset α)).filter (fun Y => ∀ y ∈ Y, π y ∈ T) =
        powersetCard a (T.map π.symm.toEmbedding) := by
      ext Y
      simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
      constructor
      · rintro ⟨hc, hY⟩
        refine ⟨fun y hy => ?_, hc⟩
        simp only [mem_map, Equiv.toEmbedding_apply]
        exact ⟨π y, hY y hy, by simp⟩
      · rintro ⟨hs, hc⟩
        refine ⟨hc, fun y hy => ?_⟩
        obtain ⟨x, hx, rfl⟩ := mem_map.mp (hs hy)
        simpa using hx
    rw [this, card_powersetCard, card_map]
  simp_rw [key]
  rw [sum_const, card_univ, Fintype.card_perm, smul_eq_mul]

lemma descFactorial_mul_pow_le {t n : ℕ} (htn : t ≤ n) (a : ℕ) :
    t.descFactorial a * n ^ a ≤ n.descFactorial a * t ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    have h2 : (t - a) * n ≤ (n - a) * t := by
      rcases le_or_gt a t with hat | hat
      · have hn : a ≤ n := hat.trans htn
        zify [hat, hn]; nlinarith
      · rw [Nat.sub_eq_zero_of_le hat.le]; simp
    calc (t - a) * t.descFactorial a * (n ^ a * n)
        = (t.descFactorial a * n ^ a) * ((t - a) * n) := by ring
      _ ≤ (n.descFactorial a * t ^ a) * ((n - a) * t) := Nat.mul_le_mul ih h2
      _ = (n - a) * n.descFactorial a * (t ^ a * t) := by ring

lemma choose_mul_pow_le {t n : ℕ} (htn : t ≤ n) (a : ℕ) :
    t.choose a * n ^ a ≤ n.choose a * t ^ a := by
  have h := descFactorial_mul_pow_le htn a
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at h
  have hpos := Nat.factorial_pos a
  have : a.factorial * (t.choose a * n ^ a) ≤ a.factorial * (n.choose a * t ^ a) := by
    calc a.factorial * (t.choose a * n ^ a) = a.factorial * t.choose a * n ^ a := by ring
      _ ≤ a.factorial * n.choose a * t ^ a := h
      _ = a.factorial * (n.choose a * t ^ a) := by ring
  exact Nat.le_of_mul_le_mul_left this hpos

/-- **Sampling without replacement.** -/
theorem permInto_mul_pow_le (Y T : Finset α) :
    permInto Y T * (Fintype.card α) ^ Y.card ≤
      (Fintype.card α).factorial * T.card ^ Y.card := by
  set n := Fintype.card α
  set a := Y.card
  have hsum := sum_permInto a T
  have hconst : ∑ Y' ∈ powersetCard a (univ : Finset α), permInto Y' T =
      n.choose a * permInto Y T := by
    rw [Finset.sum_congr rfl (g := fun _ => permInto Y T)]
    · rw [sum_const, card_powersetCard, card_univ, smul_eq_mul]
    · intro Y' hY'
      exact permInto_eq_of_card Y' Y T ((mem_powersetCard.mp hY').2.trans rfl)
  rw [hconst] at hsum
  have han : a ≤ n := by simpa [a, n] using Finset.card_le_univ Y
  have htn : T.card ≤ n := Finset.card_le_univ T
  have hpos : 0 < n.choose a := Nat.choose_pos han
  have hch := choose_mul_pow_le htn a
  have : n.choose a * (permInto Y T * n ^ a) ≤ n.choose a * (n.factorial * T.card ^ a) := by
    calc n.choose a * (permInto Y T * n ^ a) = (n.choose a * permInto Y T) * n ^ a := by ring
      _ = n.factorial * T.card.choose a * n ^ a := by rw [hsum]
      _ = n.factorial * (T.card.choose a * n ^ a) := by ring
      _ ≤ n.factorial * (n.choose a * T.card ^ a) := Nat.mul_le_mul_left _ hch
      _ = n.choose a * (n.factorial * T.card ^ a) := by ring
  exact Nat.le_of_mul_le_mul_left this hpos

end SelCount
