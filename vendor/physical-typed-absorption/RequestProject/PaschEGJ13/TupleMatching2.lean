/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.TupleMatching
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Step 3 of Theorem 1.3: concentration of tuple weights of the random matching -/

@[expose] public section

namespace Pseudorandom

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {p q : ℕ} {A : Fin p → Finset (Finset V)} {fc : Finset V → Fin q}

omit [Fintype V] in
theorem mem_tmM_update_iff {i : Fin p} {e : Finset V} (he : e ∉ A i)
    (z : Fin p → Fin q × Finset (Finset V)) (a : Fin q × Finset (Finset V)) :
    e ∈ tmM A fc (Function.update z i a) ↔ e ∈ tmM A fc z := by
  simp only [tmM, mem_biUnion, mem_univ, true_and, mem_inter, cls, mem_filter]
  constructor
  · rintro ⟨i', h1, h2, h3⟩
    have hi' : i' ≠ i := fun h => he (h ▸ h2)
    rw [Function.update_of_ne hi'] at h1 h3
    exact ⟨i', h1, h2, h3⟩
  · rintro ⟨i', h1, h2, h3⟩
    have hi' : i' ≠ i := fun h => he (h ▸ h2)
    refine ⟨i', ?_, h2, ?_⟩ <;> rw [Function.update_of_ne hi'] <;> assumption

omit [Fintype V] in
theorem tmM_subset_biUnion (z : Fin p → Fin q × Finset (Finset V)) :
    tmM A fc z ⊆ univ.biUnion (fun i => cls A fc i (z i).1) := by
  intro e he
  simp only [tmM, mem_biUnion, mem_univ, true_and, mem_inter] at he ⊢
  obtain ⟨i, -, h⟩ := he
  exact ⟨i, h⟩

open Classical in
/-- **Step 3 for tuple weights.** -/
theorem random_matching_tuple (hq : 0 < q) (H : Finset (Finset V)) (hAH : ∀ i, A i ⊆ H)
    (hne : ∀ i, ∀ e ∈ A i, e.Nonempty)
    (hdisj : ∀ i i', i ≠ i' → ∀ e ∈ A i, ∀ g ∈ A i', Disjoint e g)
    (ν : Fin p → Fin q → Finset (Finset V) → ℝ) (hν0 : ∀ i j N, 0 ≤ ν i j N)
    (hν1 : ∀ i j, ∑ N, ν i j N = 1)
    (hνsupp : ∀ i j N, ν i j N ≠ 0 → IsMatching N ∧ N ⊆ cls A fc i j)
    (x : ℝ) (hνmarg : ∀ i j, ∀ e ∈ cls A fc i j, marg (ν i j) e = x)
    {κ : Type*} (K : Finset κ) (ℓ : κ → ℕ) (W : κ → Finset (Finset V) → ℝ)
    (hW0 : ∀ k ∈ K, ∀ S ∈ H.powersetCard (ℓ k), 0 ≤ W k S)
    (c t : κ → ℝ) (hc : ∀ k ∈ K, 0 < c k) (ht : ∀ k ∈ K, 0 < t k)
    (hΓ : ∀ k ∈ K, ∀ (i : Fin p) (σ : Fin p → Fin q),
      ∑ S ∈ H.powersetCard (ℓ k), W k S *
        ((if S ⊆ univ.biUnion (fun i' => cls A fc i' (σ i')) then 1 else 0) *
          (if ∃ e ∈ S, e ∈ A i then 1 else 0)) ≤ c k)
    (hfail : ∑ k ∈ K, 2 * Real.exp (-(t k ^ 2 / (2 * (p * c k ^ 2 + c k * t k)))) < 1) :
    ∃ M ⊆ H, IsMatching M ∧ ∀ k ∈ K,
      (x / q) ^ ℓ k * (∑ S ∈ H.powersetCard (ℓ k),
          W k S * if DistinctParts A S then 1 else 0) - t k < tweight (ℓ k) (W k) M ∧
      tweight (ℓ k) (W k) M < (x / q) ^ ℓ k * (∑ S ∈ H.powersetCard (ℓ k),
          W k S * if DistinctParts A S then 1 else 0) +
        (∑ S ∈ H.powersetCard (ℓ k), W k S *
          ((x / q) ^ (partsMet A S).card *
            if InParts A S ∧ ConsCol A fc S ∧ ¬ DistinctParts A S then 1 else 0)) + t k := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set P := tmP ν with hPdef
  have hP : IsPMF P := tmP_isPMF hq hν0 hν1
  set F : κ → (Fin p → Fin q × Finset (Finset V)) → ℝ := fun k z =>
    ∑ S ∈ H.powersetCard (ℓ k), W k S * if S ⊆ tmM A fc z then 1 else 0 with hFdef
  -- expectations
  have hEF : ∀ k ∈ K, (x / q) ^ ℓ k * (∑ S ∈ H.powersetCard (ℓ k),
        W k S * if DistinctParts A S then 1 else 0) ≤ pE P (F k) ∧
      pE P (F k) ≤ (x / q) ^ ℓ k * (∑ S ∈ H.powersetCard (ℓ k),
        W k S * if DistinctParts A S then 1 else 0) +
        ∑ S ∈ H.powersetCard (ℓ k), W k S *
          ((x / q) ^ (partsMet A S).card *
            if InParts A S ∧ ConsCol A fc S ∧ ¬ DistinctParts A S then 1 else 0) := by
    intro k hk
    have hE : pE P (F k) = ∑ S ∈ H.powersetCard (ℓ k),
        W k S * pE P (fun z => if S ⊆ tmM A fc z then 1 else 0) := by
      simp only [hFdef]
      rw [pE_sum]
      exact sum_congr rfl fun S _ => pE_const_mul _ _
    rw [hE, mul_sum, ← sum_add_distrib]
    constructor
    · refine sum_le_sum fun S hS => ?_
      have hw := hW0 k hk S hS
      have hcard := (mem_powersetCard.mp hS).2
      split_ifs with hd
      · rw [prob_distinct hq hν1 hνsupp x hνmarg hne hdisj hd, hcard]; ring_nf; exact le_rfl
      · rw [mul_zero, mul_zero]
        exact mul_nonneg hw (pE_nonneg hP fun z => by split_ifs <;> norm_num)
    · refine sum_le_sum fun S hS => ?_
      have hw := hW0 k hk S hS
      have hcard := (mem_powersetCard.mp hS).2
      by_cases hd : DistinctParts A S
      · rw [prob_distinct hq hν1 hνsupp x hνmarg hne hdisj hd, hcard]
        simp [hd]; ring_nf; exact le_rfl
      · have h := prob_le hq hν0 hν1 hνsupp x hνmarg hne hdisj S
        simp only [hd, if_false, mul_zero, zero_add, not_false_eq_true, and_true]
        exact mul_le_mul_of_nonneg_left h hw
  -- bounded differences
  have hgap : ∀ k ∈ K, CoordGap (F k) (fun _ => c k) := by
    intro k hk i z a b
    set G : (Fin p → Fin q × Finset (Finset V)) → ℝ := fun z =>
      ∑ S ∈ H.powersetCard (ℓ k), W k S *
        ((if S ⊆ tmM A fc z then 1 else 0) * (if ∃ e ∈ S, e ∈ A i then 1 else 0)) with hG
    set F1 : (Fin p → Fin q × Finset (Finset V)) → ℝ := fun z =>
      ∑ S ∈ H.powersetCard (ℓ k), W k S *
        ((if S ⊆ tmM A fc z then 1 else 0) * (if ∃ e ∈ S, e ∈ A i then 0 else 1)) with hF1
    have hsplit : ∀ z, F k z = F1 z + G z := by
      intro z
      simp only [hFdef, hF1, hG]
      rw [← sum_add_distrib]
      refine sum_congr rfl fun S _ => ?_
      split_ifs <;> ring
    have hF1u : ∀ a, F1 (Function.update z i a) = F1 z := by
      intro a
      simp only [hF1]
      refine sum_congr rfl fun S _ => ?_
      by_cases hm : ∃ e ∈ S, e ∈ A i
      · simp [hm]
      · push_neg at hm
        have : S ⊆ tmM A fc (Function.update z i a) ↔ S ⊆ tmM A fc z := by
          constructor
          · intro h e he; exact (mem_tmM_update_iff (hm e he) z a).mp (h he)
          · intro h e he; exact (mem_tmM_update_iff (hm e he) z a).mpr (h he)
        simp only [this]
    have hGb : ∀ z', 0 ≤ G z' ∧ G z' ≤ c k := by
      intro z'
      constructor
      · exact sum_nonneg fun S hS => mul_nonneg (hW0 k hk S hS)
          (mul_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num))
      · refine le_trans ?_ (hΓ k hk i (fun i' => (z' i').1))
        refine sum_le_sum fun S hS => mul_le_mul_of_nonneg_left ?_ (hW0 k hk S hS)
        apply mul_le_mul_of_nonneg_right _ (by split_ifs <;> norm_num)
        split_ifs with h1 h2 h2
        · exact le_rfl
        · exact absurd (h1.trans (tmM_subset_biUnion z')) h2
        · exact zero_le_one
        · exact le_rfl
    rw [hsplit, hsplit, hF1u, hF1u]
    have h1 := hGb (Function.update z i a)
    have h2 := hGb (Function.update z i b)
    rw [abs_le]; constructor <;> linarith
  have hrare : ∀ k, CoordRare (F k) (fun _ => (univ : Finset (Fin q × Finset (Finset V)))) :=
    fun k i ω a b ha _ => absurd (mem_univ a) ha
  have hq1 : ∀ i, ∑ a ∈ (univ : Finset (Fin q × Finset (Finset V))), P i a ≤ 1 :=
    fun i => le_of_eq (hP.2 i)
  have htail : ∀ k ∈ K, pProb P (fun ω => t k ≤ F k ω - pE P (F k)) +
      pProb P (fun ω => t k ≤ pE P (F k) - F k ω) ≤
        2 * Real.exp (-(t k ^ 2 / (2 * (p * c k ^ 2 + c k * t k)))) := by
    intro k hk
    have hsum : (∑ _i : Fin p, (1 : ℝ) * c k ^ 2) = p * c k ^ 2 := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, one_mul]
    have h1 := pE_upper_tail P hP (F k) (fun _ => c k) (fun _ => 1) _ (c k) (hc k hk)
      (fun _ => ⟨(hc k hk).le, le_rfl⟩) (hgap k hk) (hrare k) hq1 (t k) (ht k hk)
    have h2 := pE_lower_tail P hP (F k) (fun _ => c k) (fun _ => 1) _ (c k) (hc k hk)
      (fun _ => ⟨(hc k hk).le, le_rfl⟩) (hgap k hk) (hrare k) hq1 (t k) (ht k hk)
    rw [hsum] at h1 h2
    linarith
  set bad : (Fin p → Fin q × Finset (Finset V)) → Prop := fun ω =>
    ∃ k ∈ K, t k ≤ F k ω - pE P (F k) ∨ t k ≤ pE P (F k) - F k ω
  have hbad : pProb P bad < 1 := by
    refine lt_of_le_of_lt ((pProb_exists_le hP K _).trans ?_) hfail
    exact sum_le_sum fun k hk => (pProb_or_le hP _ _).trans (htail k hk)
  obtain ⟨ω, hω, hgood⟩ := exists_of_pProb_lt_one hP hbad
  have hpos : ∀ i, ν i (ω i).1 (ω i).2 ≠ 0 := by
    intro i h
    have : pw P ω = 0 := by
      unfold pw
      exact prod_eq_zero (mem_univ i) (by simp [hPdef, tmP, h])
    linarith
  have hsupp : ∀ i, IsMatching (ω i).2 ∧ (ω i).2 ⊆ cls A fc i (ω i).1 := fun i =>
    hνsupp i _ _ (hpos i)
  have hMH : tmM A fc ω ⊆ H := by
    intro e he
    obtain ⟨i, hi, -⟩ := tmM_inParts ω he
    exact hAH i hi
  have hweight : ∀ k, tweight (ℓ k) (W k) (tmM A fc ω) = F k ω := by
    intro k
    simp only [tweight, hFdef]
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext S
    simp only [mem_powersetCard, mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1.trans hMH, h2⟩, h1⟩
    · rintro ⟨⟨-, h2⟩, h1⟩; exact ⟨h1, h2⟩
  refine ⟨tmM A fc ω, hMH, ?_, fun k hk => ?_⟩
  · intro e he f hf hef
    obtain ⟨i, hi, hzi, -⟩ := tmM_inParts ω he
    obtain ⟨i', hi', hzi', -⟩ := tmM_inParts ω hf
    by_cases hii : i = i'
    · subst hii
      exact (hsupp i).1 e hzi f hzi' hef
    · exact hdisj i i' hii e hi f hi'
  · rw [hweight]
    have h1 : ¬ (t k ≤ F k ω - pE P (F k)) := fun h => hgood ⟨k, hk, Or.inl h⟩
    have h2 : ¬ (t k ≤ pE P (F k) - F k ω) := fun h => hgood ⟨k, hk, Or.inr h⟩
    push_neg at h1 h2
    have := hEF k hk
    constructor <;> linarith

end Pseudorandom
