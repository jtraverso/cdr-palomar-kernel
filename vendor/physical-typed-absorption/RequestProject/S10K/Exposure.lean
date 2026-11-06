/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# V23 / S05 §3: finite sequential exposure and the first-arrival bound

A finite random process with `m` queries. Query `k` chooses UNIFORMLY from a finite nonempty
option set `opts h` that depends on the history `h` (the list of previous answers). The
probability of a full answer sequence `ω : Fin m → α` is the product of the conditional
uniform weights (`wt`). Nothing about independence between different processes is used:
every source triangle will get its OWN process.

* `sum_wt`: the weights are a probability distribution.
* `marginal_const`: a coordinate whose option set does not depend on the history is
  uniform on that set (used for the three conditioned pivots).
* `mem_opts_of_wt_ne_zero`: every coordinate of a positive-weight sequence is a legal answer
  for its own history.
* `exposure_bound` (**first-arrival bound**, S05 (8)⇒(9)): if every query, for every
  history, puts a fixed nonempty set `W` (`|W| ≤ r₀`) of not-yet-exposed vertices inside its
  revealed set with probability `≤ q^|W|`, then a fixed set `U` (`|U| ≤ r₀`) of unexposed
  vertices is covered by all revealed sets with probability `≤ (m q)^|U|`.

No geometric input is used in this file.
-/

open Finset

noncomputable section

namespace S10V23.Expo

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Weight of the continuation `ω` (length `m`) after history `h`: product of the
conditional uniform probabilities. -/
def wt (opts : List α → Finset α) : (m : ℕ) → List α → (Fin m → α) → ℝ
  | 0, _, _ => 1
  | m + 1, h, ω =>
    (if ω 0 ∈ opts h then ((opts h).card : ℝ)⁻¹ else 0) * wt opts m (h ++ [ω 0]) (Fin.tail ω)

omit [DecidableEq α] in
lemma sum_fin_succ {β : Type*} [AddCommMonoid β] {m : ℕ} (F : (Fin (m + 1) → α) → β) :
    ∑ ω, F ω = ∑ a, ∑ ω' : Fin m → α, F (Fin.cons a ω') := by
  rw [← (Fin.consEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type]
  rfl

omit [Fintype α] in
lemma wt_nonneg (opts : List α → Finset α) : ∀ (m : ℕ) (h : List α) (ω : Fin m → α),
    0 ≤ wt opts m h ω
  | 0, _, _ => by simp [wt]
  | m + 1, h, ω => by
    simp only [wt]
    refine mul_nonneg ?_ (wt_nonneg opts m _ _)
    split_ifs <;> positivity

/-- One-step expansion of an expectation. -/
lemma sum_wt_succ (opts : List α → Finset α) (m : ℕ) (h : List α) (G : (Fin (m + 1) → α) → ℝ) :
    ∑ ω, wt opts (m + 1) h ω * G ω =
      ∑ a ∈ opts h, ((opts h).card : ℝ)⁻¹ *
        ∑ ω' : Fin m → α, wt opts m (h ++ [a]) ω' * G (Fin.cons a ω') := by
  rw [sum_fin_succ]
  simp only [wt, Fin.cons_zero, Fin.tail_cons]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun a => a ∈ opts h)]
  rw [Finset.sum_eq_zero (s := univ.filter (fun a => a ∉ opts h)) (fun a ha => by
    simp [(Finset.mem_filter.1 ha).2])]
  rw [add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  simp [ha, mul_assoc]

/-- The weights form a probability distribution. -/
theorem sum_wt (opts : List α → Finset α) (hne : ∀ h, (opts h).Nonempty) :
    ∀ (m : ℕ) (h : List α), ∑ ω : Fin m → α, wt opts m h ω = 1
  | 0, h => by simp [wt]
  | m + 1, h => by
    have := sum_wt_succ opts m h (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    simp only [sum_wt opts hne m, mul_one, Finset.sum_const, nsmul_eq_mul]
    have : ((opts h).card : ℝ) ≠ 0 := by exact_mod_cast (hne h).card_pos.ne'
    field_simp

/-- **Marginal of a history-independent coordinate.** -/
theorem marginal_const (opts : List α → Finset α) (hne : ∀ h, (opts h).Nonempty)
    (s : Finset α) (x : α) :
    ∀ (k m : ℕ) (h : List α) (hk : k < m),
      (∀ h' : List α, h'.length = h.length + k → opts h' = s) →
      ∑ ω : Fin m → α, wt opts m h ω * (if ω ⟨k, hk⟩ = x then 1 else 0) =
        if x ∈ s then ((s.card : ℝ))⁻¹ else 0
  | k, 0, h, hk, _ => absurd hk (Nat.not_lt_zero _)
  | 0, m + 1, h, hk, hs => by
    rw [sum_wt_succ]
    have hsh : opts h = s := hs h (by simp)
    have key : ∀ a, ∑ ω' : Fin m → α, wt opts m (h ++ [a]) ω' *
        (if (Fin.cons a ω' : Fin (m + 1) → α) ⟨0, hk⟩ = x then 1 else 0) =
        if a = x then 1 else 0 := by
      intro a
      have e : ∀ ω' : Fin m → α, (Fin.cons a ω' : Fin (m + 1) → α) ⟨0, hk⟩ = a := fun _ => rfl
      simp only [e]
      split_ifs <;> simp [sum_wt opts hne m]
    simp only [key]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq', hsh]
  | k + 1, m + 1, h, hk, hs => by
    rw [sum_wt_succ]
    have hk' : k < m := by omega
    have key : ∀ a, ∑ ω' : Fin m → α, wt opts m (h ++ [a]) ω' *
        (if (Fin.cons a ω' : Fin (m + 1) → α) ⟨k + 1, hk⟩ = x then 1 else 0) =
        if x ∈ s then ((s.card : ℝ))⁻¹ else 0 := by
      intro a
      have := marginal_const opts hne s x k m (h ++ [a]) hk' (fun h' hl => hs h' (by
        simp at hl; omega))
      rw [← this]
      refine Finset.sum_congr rfl fun ω' _ => ?_
      congr 2
    simp only [key, Finset.sum_const, nsmul_eq_mul]
    have : ((opts h).card : ℝ) ≠ 0 := by exact_mod_cast (hne h).card_pos.ne'
    field_simp

/-- Prefix of length `k` of a sequence, as a history list. -/
def pre {m : ℕ} (ω : Fin m → α) (k : ℕ) (hk : k ≤ m) : List α :=
  List.ofFn (fun i : Fin k => ω (Fin.castLE hk i))

omit [Fintype α] [DecidableEq α] in
lemma pre_length {m : ℕ} (ω : Fin m → α) (k : ℕ) (hk : k ≤ m) : (pre ω k hk).length = k := by
  simp [pre]

omit [Fintype α] [DecidableEq α] in
lemma pre_getD {m : ℕ} (ω : Fin m → α) (k : ℕ) (hk : k ≤ m) (j : ℕ) (hj : j < k) (d : α) :
    (pre ω k hk).getD j d = ω ⟨j, by omega⟩ := by
  simp [pre, List.getD_eq_getElem?_getD, hj]

omit [Fintype α] [DecidableEq α] in
lemma pre_cons_succ {m : ℕ} (a : α) (ω' : Fin m → α) (k : ℕ) (hk : k + 1 ≤ m + 1) :
    pre (Fin.cons a ω' : Fin (m + 1) → α) (k + 1) hk = a :: pre ω' k (by omega) := by
  simp only [pre, List.ofFn_succ]
  congr 1

omit [Fintype α] in
/-- **Every coordinate of a positive-weight sequence is a legal answer.** -/
theorem mem_opts_of_wt_ne_zero (opts : List α → Finset α) :
    ∀ (m : ℕ) (h : List α) (ω : Fin m → α), wt opts m h ω ≠ 0 →
      ∀ (k : ℕ) (hk : k < m), ω ⟨k, hk⟩ ∈ opts (h ++ pre ω k hk.le)
  | 0, _, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | m + 1, h, ω, hw, k, hk => by
    simp only [wt] at hw
    have h1 : ω 0 ∈ opts h := by
      by_contra hc; simp [hc] at hw
    have h2 : wt opts m (h ++ [ω 0]) (Fin.tail ω) ≠ 0 := fun h0 => hw (by simp [h0])
    rcases k with _ | k
    · simpa [pre] using h1
    · have := mem_opts_of_wt_ne_zero opts m (h ++ [ω 0]) (Fin.tail ω) h2 k (by omega)
      have hω : ω = Fin.cons (ω 0) (Fin.tail ω) := (Fin.cons_self_tail ω).symm
      have e1 : pre ω (k + 1) hk.le = ω 0 :: pre (Fin.tail ω) k (by omega) := by
        conv_lhs => rw [hω]
        exact pre_cons_succ _ _ _ _
      rw [e1]
      simpa [Fin.tail] using this

/-! ## First-arrival bound -/

variable {V : Type*} [DecidableEq V]

/-- All vertices revealed by a full answer sequence. -/
def aux {m : ℕ} (vs : α → Finset V) (ω : Fin m → α) : Finset V := univ.biUnion (fun k => vs (ω k))

omit [Fintype α] [DecidableEq α] in
lemma aux_cons {m : ℕ} (vs : α → Finset V) (a : α) (ω' : Fin m → α) :
    aux vs (Fin.cons a ω' : Fin (m + 1) → α) = vs a ∪ aux vs ω' := by
  ext x
  simp only [aux, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union,
    Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]

/-- **First-arrival / sequential exposure bound** (S05 §3). `H h` is the set of exposed
vertices after history `h`; it must contain what each answer reveals. -/
theorem exposure_bound (opts : List α → Finset α) (hne : ∀ h, (opts h).Nonempty)
    (vs : α → Finset V) (H : List α → Finset V) (hH : ∀ h a, H (h ++ [a]) ⊆ H h ∪ vs a)
    {q : ℝ} (hq : 0 ≤ q) (r₀ : ℕ)
    (hstep : ∀ h (W : Finset V), W.Nonempty → W.card ≤ r₀ → Disjoint W (H h) →
      (((opts h).filter (fun a => W ⊆ vs a)).card : ℝ) ≤ q ^ W.card * (opts h).card) :
    ∀ (m : ℕ) (h : List α) (U : Finset V), U.card ≤ r₀ → Disjoint U (H h) →
      ∑ ω : Fin m → α, wt opts m h ω * (if U ⊆ aux vs ω then 1 else 0) ≤
        ((m : ℝ) * q) ^ U.card
  | 0, h, U, _, _ => by
    simp only [wt, one_mul, Finset.univ_unique, Finset.sum_singleton, CharP.cast_eq_zero,
      zero_mul]
    by_cases hU : U = ∅
    · subst hU; simp
    · have : ¬ U ⊆ aux vs (default : Fin 0 → α) := by
        intro hs
        apply hU
        have : aux vs (default : Fin 0 → α) = ∅ := by simp [aux]
        rw [this] at hs
        exact Finset.subset_empty.1 hs
      rw [if_neg this]
      exact pow_nonneg le_rfl _
  | m + 1, h, U, hU, hdis => by
    rw [sum_wt_succ]
    have hpos : (0 : ℝ) < (opts h).card := by exact_mod_cast (hne h).card_pos
    set p : ℝ := ((opts h).card : ℝ)⁻¹ with hp
    have hp0 : 0 ≤ p := by positivity
    -- inductive bound for each first answer
    have hIH : ∀ a ∈ opts h, ∑ ω' : Fin m → α, wt opts m (h ++ [a]) ω' *
        (if U ⊆ aux vs (Fin.cons a ω' : Fin (m + 1) → α) then 1 else 0) ≤
        ((m : ℝ) * q) ^ (U \ vs a).card := by
      intro a _
      have hd : Disjoint (U \ vs a) (H (h ++ [a])) := by
        refine Finset.disjoint_left.2 fun x hx hxH => ?_
        rcases Finset.mem_union.1 (hH h a hxH) with h1 | h1
        · exact Finset.disjoint_left.1 hdis (Finset.mem_sdiff.1 hx).1 h1
        · exact (Finset.mem_sdiff.1 hx).2 h1
      have := exposure_bound opts hne vs H hH hq r₀ hstep m (h ++ [a]) (U \ vs a)
        ((Finset.card_le_card Finset.sdiff_subset).trans hU) hd
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl fun ω' _ => ?_
      congr 2
      rw [aux_cons]
      exact propext ⟨fun hs x hx => by
          rcases Finset.mem_union.1 (hs (Finset.mem_sdiff.1 hx).1) with h1 | h1
          · exact absurd h1 (Finset.mem_sdiff.1 hx).2
          · exact h1,
        fun hs x hx => by
          by_cases hxa : x ∈ vs a
          · exact Finset.mem_union_left _ hxa
          · exact Finset.mem_union_right _ (hs (Finset.mem_sdiff.2 ⟨hx, hxa⟩))⟩
    set c : Finset V → ℝ := fun W => ((m : ℝ) * q) ^ (U.card - W.card) with hc
    have hc0 : ∀ W, 0 ≤ c W := fun W => pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hq) _
    -- the power is dominated by the sum over subsets
    have hdom : ∀ a, ((m : ℝ) * q) ^ (U \ vs a).card ≤
        ∑ W ∈ U.powerset, (if W ⊆ vs a then 1 else 0) * c W := by
      intro a
      have hmem : U ∩ vs a ∈ U.powerset := Finset.mem_powerset.2 Finset.inter_subset_left
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun W =>
        (if W ⊆ vs a then (1 : ℝ) else 0) * c W)
        (fun W _ => mul_nonneg (by split_ifs <;> norm_num) (hc0 W)) hmem)
      simp only [Finset.inter_subset_right, if_true, one_mul, hc]
      congr 1
      have h1 := Finset.card_sdiff_add_card_inter U (vs a)
      omega
    calc ∑ a ∈ opts h, p * ∑ ω' : Fin m → α, wt opts m (h ++ [a]) ω' *
            (if U ⊆ aux vs (Fin.cons a ω' : Fin (m + 1) → α) then 1 else 0)
        ≤ ∑ a ∈ opts h, p * ∑ W ∈ U.powerset, (if W ⊆ vs a then 1 else 0) * c W := by
          refine Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left ?_ hp0
          exact (hIH a ha).trans (hdom a)
      _ = ∑ W ∈ U.powerset, c W * (p * ((opts h).filter (fun a => W ⊆ vs a)).card) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun W _ => ?_
          rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          split_ifs <;> simp [mul_comm]
      _ ≤ ∑ W ∈ U.powerset, q ^ W.card * ((m : ℝ) * q) ^ (U.card - W.card) := by
          refine Finset.sum_le_sum fun W hW => ?_
          rw [mul_comm (q ^ W.card)]
          refine mul_le_mul_of_nonneg_left ?_ (hc0 W)
          rcases W.eq_empty_or_nonempty with hW0 | hW0
          · subst hW0
            rw [Finset.filter_true_of_mem (fun _ _ => Finset.empty_subset _)]
            simp only [Finset.card_empty, pow_zero, hp]
            rw [inv_mul_cancel₀ hpos.ne']
          · have hWU := Finset.mem_powerset.1 hW
            have := hstep h W hW0 ((Finset.card_le_card hWU).trans hU)
              (Finset.disjoint_of_subset_left hWU hdis)
            calc p * (((opts h).filter (fun a => W ⊆ vs a)).card : ℝ)
                ≤ p * (q ^ W.card * (opts h).card) := mul_le_mul_of_nonneg_left this hp0
              _ = q ^ W.card := by rw [hp]; field_simp
      _ = (((m + 1 : ℕ) : ℝ) * q) ^ U.card := by
          rw [Finset.sum_pow_mul_eq_add_pow]
          congr 1
          push_cast; ring

end S10V23.Expo
