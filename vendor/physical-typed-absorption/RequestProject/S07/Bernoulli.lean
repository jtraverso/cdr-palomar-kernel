/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# V24 / S07 §2: the full finite Bernoulli process and bounded differences

The random subset `W ⊆ U` keeps each vertex independently with probability `q`. Everything is
an explicit finite sum over `U.powerset` with weights `q^|W| (1-q)^(|U|-|W|)`; there is NO
supplied concentration provider.

* `bexp q U f` — expectation; `bexp_insert` reveals one coordinate.
* `bexp_subset_ind` — `P(S ⊆ W) = q^|S|`.
* `mgf_lower` — **bounded differences (McDiarmid type), proved by revealing coordinates one at a
  time**: if `|f(W ∪ {a}) - f(W)| ≤ c a` and `λ c a ≤ 1`, then
  `E exp(-λ (f - E f)) ≤ exp(λ² Σ c_a²)`. The one-coordinate step uses only
  `|e^x - 1 - x| ≤ x²` for `|x| ≤ 1`.
* `tail_lower`, `tail_upper` — the corresponding tail bounds.
* `exists_good` — the finite union bound: if the bad probabilities sum to `< 1`, a single `W`
  avoids all of them.
* `count_tail` — containment counts `X(W) = #{i ∈ I : e i ⊆ W}` with `|e i| ≤ r` and
  vertex degrees `≤ Δ`: `P(X(W) < L q^r / 2) ≤ exp(-L q^(2r) / (16 Δ r))` when `|I| ≥ L`.
-/

open Finset

namespace S07V24

variable {V : Type*} [DecidableEq V]

/-- Bernoulli(`q`) expectation over subsets of `U` -/
noncomputable def bexp (q : ℝ) (U : Finset V) (f : Finset V → ℝ) : ℝ :=
  ∑ W ∈ U.powerset, q ^ W.card * (1 - q) ^ (U.card - W.card) * f W

/-- Bernoulli(`q`) probability of an event -/
noncomputable def bprob (q : ℝ) (U : Finset V) (E : Finset V → Prop) [DecidablePred E] : ℝ :=
  bexp q U fun W => if E W then 1 else 0

variable {q : ℝ}

omit [DecidableEq V] in
lemma bweight_nonneg (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (U W : Finset V) :
    0 ≤ q ^ W.card * (1 - q) ^ (U.card - W.card) :=
  mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (by linarith) _)

omit [DecidableEq V] in
lemma bexp_empty (f : Finset V → ℝ) : bexp q ∅ f = f ∅ := by
  simp [bexp]

lemma bexp_insert {a : V} {U : Finset V} (ha : a ∉ U) (f : Finset V → ℝ) :
    bexp q (insert a U) f = (1 - q) * bexp q U f + q * bexp q U (fun W => f (insert a W)) := by
  unfold bexp
  rw [Finset.sum_powerset_insert ha, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro W hW
    rw [Finset.mem_powerset] at hW
    have hc := Finset.card_le_card hW
    rw [Finset.card_insert_of_notMem ha, show U.card + 1 - W.card = (U.card - W.card) + 1 by omega,
      pow_succ]; ring
  · apply Finset.sum_congr rfl; intro W hW
    rw [Finset.mem_powerset] at hW
    have haW : a ∉ W := fun h => ha (hW h)
    rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haW,
      show U.card + 1 - (W.card + 1) = U.card - W.card by omega, pow_succ]; ring

omit [DecidableEq V] in
lemma bexp_congr {U : Finset V} {f g : Finset V → ℝ} (h : ∀ W ⊆ U, f W = g W) :
    bexp q U f = bexp q U g := by
  unfold bexp; apply Finset.sum_congr rfl; intro W hW; rw [h W (Finset.mem_powerset.1 hW)]

omit [DecidableEq V] in
lemma bexp_mono (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {U : Finset V} {f g : Finset V → ℝ}
    (h : ∀ W ⊆ U, f W ≤ g W) : bexp q U f ≤ bexp q U g := by
  unfold bexp; apply Finset.sum_le_sum; intro W hW
  exact mul_le_mul_of_nonneg_left (h W (Finset.mem_powerset.1 hW)) (bweight_nonneg hq0 hq1 U W)

omit [DecidableEq V] in
lemma bexp_add (U : Finset V) (f g : Finset V → ℝ) :
    bexp q U (fun W => f W + g W) = bexp q U f + bexp q U g := by
  unfold bexp; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro W _; ring

omit [DecidableEq V] in
lemma bexp_smul (U : Finset V) (r : ℝ) (f : Finset V → ℝ) :
    bexp q U (fun W => r * f W) = r * bexp q U f := by
  unfold bexp; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro W _; ring

omit [DecidableEq V] in
lemma bexp_neg (U : Finset V) (f : Finset V → ℝ) :
    bexp q U (fun W => -f W) = -bexp q U f := by
  have := bexp_smul (q := q) U (-1) f; simpa using this

omit [DecidableEq V] in
lemma bexp_sub (U : Finset V) (f g : Finset V → ℝ) :
    bexp q U (fun W => f W - g W) = bexp q U f - bexp q U g := by
  simp only [sub_eq_add_neg]; rw [bexp_add, bexp_neg]

omit [DecidableEq V] in
lemma bexp_const (U : Finset V) (r : ℝ) : bexp q U (fun _ => r) = r := by
  unfold bexp
  rw [← Finset.sum_mul, Finset.sum_pow_mul_eq_add_pow, add_sub_cancel, one_pow, one_mul]

omit [DecidableEq V] in
lemma bexp_sum {ι : Type*} (U : Finset V) (I : Finset ι) (F : ι → Finset V → ℝ) :
    bexp q U (fun W => ∑ i ∈ I, F i W) = ∑ i ∈ I, bexp q U (F i) := by
  unfold bexp; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro W _
  rw [Finset.mul_sum]

omit [DecidableEq V] in
lemma bexp_nonneg (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {U : Finset V} {f : Finset V → ℝ}
    (h : ∀ W ⊆ U, 0 ≤ f W) : 0 ≤ bexp q U f := by
  have := bexp_mono hq0 hq1 (f := fun _ => 0) h; rwa [bexp_const] at this

/-- `P(S ⊆ W) = q^|S|` -/
theorem bexp_subset_ind (U : Finset V) :
    ∀ S ⊆ U, bexp q U (fun W => if S ⊆ W then 1 else 0) = q ^ S.card := by
  induction U using Finset.induction_on with
  | empty => intro S hS; rw [Finset.subset_empty] at hS; subst hS; simp [bexp_empty]
  | insert a U ha ih =>
    intro S hS
    rw [bexp_insert ha]
    by_cases haS : a ∈ S
    · have h1 : bexp q U (fun W => if S ⊆ W then (1 : ℝ) else 0) = 0 := by
        rw [bexp_congr (g := fun _ => 0)]; · exact bexp_const U 0
        intro W hW; rw [if_neg]; intro h; exact ha (hW (h haS))
      have hS' : S.erase a ⊆ U := by
        intro b hb; have := hS (Finset.mem_of_mem_erase hb)
        rcases Finset.mem_insert.1 this with h | h
        · exact absurd h (Finset.ne_of_mem_erase hb)
        · exact h
      have h2 : bexp q U (fun W => if S ⊆ insert a W then (1 : ℝ) else 0) =
          bexp q U (fun W => if S.erase a ⊆ W then (1 : ℝ) else 0) := by
        apply bexp_congr; intro W hW
        have haW : a ∉ W := fun h => ha (hW h)
        congr 1; apply propext; exact Finset.subset_insert_iff
      rw [h1, h2, ih _ hS', Finset.card_erase_of_mem haS]
      have : 0 < S.card := Finset.card_pos.2 ⟨a, haS⟩
      rw [mul_zero, zero_add, ← pow_succ', Nat.sub_add_cancel this]
    · have hS' : S ⊆ U := by
        intro b hb; have := hS hb
        rcases Finset.mem_insert.1 this with h | h
        · exact absurd (h ▸ hb) haS
        · exact h
      have h2 : bexp q U (fun W => if S ⊆ insert a W then (1 : ℝ) else 0) =
          bexp q U (fun W => if S ⊆ W then (1 : ℝ) else 0) := by
        apply bexp_congr; intro W _
        congr 1; apply propext
        constructor
        · intro h b hb; rcases Finset.mem_insert.1 (h hb) with h' | h'
          · exact absurd (h' ▸ hb) haS
          · exact h'
        · intro h; exact h.trans (Finset.subset_insert a W)
      rw [h2, ih _ hS']; ring

/-! ### The one-coordinate step -/

lemma exp_le_quad {x : ℝ} (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le hx
  have := (abs_le.1 this).2; linarith

lemma two_point (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {l δ c : ℝ} (hl : 0 ≤ l) (hδ : |δ| ≤ c)
    (hlc : l * c ≤ 1) :
    (1 - q) * Real.exp (l * q * δ) + q * Real.exp (-(l * (1 - q) * δ)) ≤
      Real.exp (l ^ 2 * c ^ 2) := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hδ
  have hld : |l * δ| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hl]; exact (mul_le_mul_of_nonneg_left hδ hl).trans hlc
  have h1 : |l * q * δ| ≤ 1 := by
    rw [show l * q * δ = q * (l * δ) by ring, abs_mul, abs_of_nonneg hq0]
    exact (mul_le_mul hq1 hld (abs_nonneg _) zero_le_one).trans (by norm_num)
  have h2 : |-(l * (1 - q) * δ)| ≤ 1 := by
    rw [abs_neg, show l * (1 - q) * δ = (1 - q) * (l * δ) by ring, abs_mul,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - q)]
    exact (mul_le_mul (by linarith) hld (abs_nonneg _) zero_le_one).trans (by norm_num)
  have e1 := exp_le_quad h1
  have e2 := exp_le_quad h2
  have hδ2 : δ ^ 2 ≤ c ^ 2 := by
    have := sq_abs δ; rw [← this]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
  have hq' : 0 ≤ 1 - q := by linarith
  calc (1 - q) * Real.exp (l * q * δ) + q * Real.exp (-(l * (1 - q) * δ))
      ≤ (1 - q) * (1 + l * q * δ + (l * q * δ) ^ 2) +
          q * (1 + -(l * (1 - q) * δ) + (-(l * (1 - q) * δ)) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hq') (mul_le_mul_of_nonneg_left e2 hq0)
    _ = 1 + l ^ 2 * δ ^ 2 * (q * (1 - q)) := by ring
    _ ≤ 1 + l ^ 2 * c ^ 2 := by
        have : q * (1 - q) ≤ 1 := by nlinarith
        have h3 : 0 ≤ l ^ 2 * δ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hδ2 (sq_nonneg l)]
    _ ≤ Real.exp (l ^ 2 * c ^ 2) := by linarith [Real.add_one_le_exp (l ^ 2 * c ^ 2)]

/-- **Bounded differences, lower-tail exponential moment.** -/
theorem mgf_lower (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : V → ℝ) {l : ℝ} (hl : 0 ≤ l) :
    ∀ (U : Finset V) (f : Finset V → ℝ),
      (∀ W ⊆ U, ∀ a ∈ U, a ∉ W → |f (insert a W) - f W| ≤ c a) →
      (∀ a ∈ U, l * c a ≤ 1) →
      bexp q U (fun W => Real.exp (-(l * (f W - bexp q U f)))) ≤
        Real.exp (l ^ 2 * ∑ a ∈ U, c a ^ 2) := by
  intro U
  induction U using Finset.induction_on with
  | empty => intro f _ _; simp [bexp_empty]
  | insert a U ha ih =>
    intro f hf hlc
    set f1 : Finset V → ℝ := fun W => f (insert a W)
    have hf0 : ∀ W ⊆ U, ∀ b ∈ U, b ∉ W → |f (insert b W) - f W| ≤ c b :=
      fun W hW b hb hbW => hf W (hW.trans (Finset.subset_insert a U)) b
        (Finset.mem_insert_of_mem hb) hbW
    have hf1 : ∀ W ⊆ U, ∀ b ∈ U, b ∉ W → |f1 (insert b W) - f1 W| ≤ c b := by
      intro W hW b hb hbW
      have hab : b ≠ a := fun h => ha (h ▸ hb)
      simp only [f1]; rw [Finset.insert_comm a b W]
      apply hf (insert a W) (Finset.insert_subset_insert a hW) b (Finset.mem_insert_of_mem hb)
      rw [Finset.mem_insert, not_or]; exact ⟨hab, hbW⟩
    have hlc' : ∀ b ∈ U, l * c b ≤ 1 := fun b hb => hlc b (Finset.mem_insert_of_mem hb)
    set m0 := bexp q U f
    set m1 := bexp q U f1
    have hm : bexp q (insert a U) f = (1 - q) * m0 + q * m1 := bexp_insert ha f
    have hδ : |m1 - m0| ≤ c a := by
      rw [← bexp_sub]
      have hle : ∀ W ⊆ U, |f1 W - f W| ≤ c a := fun W hW =>
        hf W (hW.trans (Finset.subset_insert a U)) a (Finset.mem_insert_self a U)
          (fun h => ha (hW h))
      rw [abs_le]; constructor
      · have := bexp_mono hq0 hq1 (U := U) (f := fun _ => -c a) (g := fun W => f1 W - f W)
          (fun W hW => (abs_le.1 (hle W hW)).1)
        rwa [bexp_const] at this
      · have := bexp_mono hq0 hq1 (U := U) (f := fun W => f1 W - f W) (g := fun _ => c a)
          (fun W hW => (abs_le.1 (hle W hW)).2)
        rwa [bexp_const] at this
    rw [bexp_insert ha, hm]
    have I0 := ih f hf0 hlc'
    have I1 := ih f1 hf1 hlc'
    set S := ∑ b ∈ U, c b ^ 2
    have e0 : bexp q U (fun W => Real.exp (-(l * (f W - ((1 - q) * m0 + q * m1))))) =
        Real.exp (l * q * (m1 - m0)) * bexp q U (fun W => Real.exp (-(l * (f W - m0)))) := by
      rw [← bexp_smul U (Real.exp (l * q * (m1 - m0)))
        (fun W => Real.exp (-(l * (f W - m0))))]
      apply bexp_congr; intro W _; rw [← Real.exp_add]; congr 1; ring
    have e1 : bexp q U (fun W => Real.exp (-(l * (f (insert a W) - ((1 - q) * m0 + q * m1))))) =
        Real.exp (-(l * (1 - q) * (m1 - m0))) *
          bexp q U (fun W => Real.exp (-(l * (f1 W - m1)))) := by
      rw [← bexp_smul U (Real.exp (-(l * (1 - q) * (m1 - m0))))
        (fun W => Real.exp (-(l * (f1 W - m1))))]
      apply bexp_congr; intro W _; rw [← Real.exp_add]; congr 1
      simp only [f1]; ring
    rw [e0, e1]
    have hq' : 0 ≤ 1 - q := by linarith
    have tp := two_point hq0 hq1 hl hδ (hlc a (Finset.mem_insert_self a U))
    calc (1 - q) * (Real.exp (l * q * (m1 - m0)) *
            bexp q U (fun W => Real.exp (-(l * (f W - m0))))) +
          q * (Real.exp (-(l * (1 - q) * (m1 - m0))) *
            bexp q U (fun W => Real.exp (-(l * (f1 W - m1)))))
        ≤ (1 - q) * (Real.exp (l * q * (m1 - m0)) * Real.exp (l ^ 2 * S)) +
          q * (Real.exp (-(l * (1 - q) * (m1 - m0))) * Real.exp (l ^ 2 * S)) := by
          gcongr
      _ = ((1 - q) * Real.exp (l * q * (m1 - m0)) +
            q * Real.exp (-(l * (1 - q) * (m1 - m0)))) * Real.exp (l ^ 2 * S) := by ring
      _ ≤ Real.exp (l ^ 2 * c a ^ 2) * Real.exp (l ^ 2 * S) :=
          mul_le_mul_of_nonneg_right tp (Real.exp_pos _).le
      _ = Real.exp (l ^ 2 * ∑ b ∈ insert a U, c b ^ 2) := by
          rw [← Real.exp_add, Finset.sum_insert ha, mul_add]

/-- lower tail -/
theorem tail_lower (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : V → ℝ) {l : ℝ} (hl : 0 ≤ l)
    (U : Finset V) (f : Finset V → ℝ)
    (hf : ∀ W ⊆ U, ∀ a ∈ U, a ∉ W → |f (insert a W) - f W| ≤ c a)
    (hlc : ∀ a ∈ U, l * c a ≤ 1) (s : ℝ) :
    bprob q U (fun W => f W ≤ bexp q U f - s) ≤
      Real.exp (-(l * s) + l ^ 2 * ∑ a ∈ U, c a ^ 2) := by
  unfold bprob
  have hM := mgf_lower hq0 hq1 c hl U f hf hlc
  calc bexp q U (fun W => if f W ≤ bexp q U f - s then 1 else 0)
      ≤ bexp q U (fun W => Real.exp (-(l * s)) * Real.exp (-(l * (f W - bexp q U f)))) := by
        apply bexp_mono hq0 hq1; intro W _
        split_ifs with h
        · rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
        · positivity
    _ = Real.exp (-(l * s)) * bexp q U (fun W => Real.exp (-(l * (f W - bexp q U f)))) :=
        bexp_smul _ _ _
    _ ≤ Real.exp (-(l * s)) * Real.exp (l ^ 2 * ∑ a ∈ U, c a ^ 2) :=
        mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]

/-- upper tail -/
theorem tail_upper (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : V → ℝ) {l : ℝ} (hl : 0 ≤ l)
    (U : Finset V) (f : Finset V → ℝ)
    (hf : ∀ W ⊆ U, ∀ a ∈ U, a ∉ W → |f (insert a W) - f W| ≤ c a)
    (hlc : ∀ a ∈ U, l * c a ≤ 1) (s : ℝ) :
    bprob q U (fun W => bexp q U f + s ≤ f W) ≤
      Real.exp (-(l * s) + l ^ 2 * ∑ a ∈ U, c a ^ 2) := by
  have := tail_lower hq0 hq1 c hl U (fun W => -f W) (fun W hW a ha haW => by
    rw [show -f (insert a W) - -f W = -(f (insert a W) - f W) by ring, abs_neg]
    exact hf W hW a ha haW) hlc s
  unfold bprob at this ⊢
  rw [bexp_neg] at this
  convert this using 2; ext W; congr 1; apply propext; constructor <;> intro h <;> linarith

omit [DecidableEq V] in
/-- **finite union bound** -/
theorem exists_good (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (U : Finset V) {ι : Type*} (T : Finset ι)
    (bad : ι → Finset V → Prop) [∀ i, DecidablePred (bad i)]
    (h : ∑ i ∈ T, bprob q U (bad i) < 1) : ∃ W ⊆ U, ∀ i ∈ T, ¬ bad i W := by
  by_contra hne
  push_neg at hne
  have hle : bexp q U (fun _ => (1 : ℝ)) ≤ ∑ i ∈ T, bprob q U (bad i) := by
    unfold bprob; rw [← bexp_sum]
    apply bexp_mono hq0 hq1; intro W hW
    obtain ⟨i, hi, hb⟩ := hne W hW
    calc (1 : ℝ) = if bad i W then 1 else 0 := by rw [if_pos hb]
      _ ≤ ∑ j ∈ T, if bad j W then 1 else 0 :=
          Finset.single_le_sum (f := fun j => if bad j W then (1 : ℝ) else 0)
            (fun j _ => by split_ifs <;> norm_num) hi
  rw [bexp_const] at hle; linarith

/-! ### Containment counts -/

/-- number of members of the family contained in `W` -/
def ccount {ι : Type*} (I : Finset ι) (e : ι → Finset V) (W : Finset V) : ℕ :=
  (I.filter fun i => e i ⊆ W).card

lemma ccount_diff {ι : Type*} [DecidableEq ι] (I : Finset ι) (e : ι → Finset V) (W : Finset V) (a : V) :
    |(ccount I e (insert a W) : ℝ) - ccount I e W| ≤ (I.filter fun i => a ∈ e i).card := by
  unfold ccount
  have hsub : (I.filter fun i => e i ⊆ W) ⊆ I.filter fun i => e i ⊆ insert a W := by
    intro i hi; simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.trans (Finset.subset_insert a W)⟩
  have hdiff : (I.filter fun i => e i ⊆ insert a W) \ (I.filter fun i => e i ⊆ W) ⊆
      I.filter fun i => a ∈ e i := by
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_filter] at hi ⊢
    refine ⟨hi.1.1, ?_⟩
    by_contra hai
    exact hi.2 ⟨hi.1.1, fun b hb => by
      rcases Finset.mem_insert.1 (hi.1.2 hb) with h | h
      · exact absurd (h ▸ hb) hai
      · exact h⟩
  have h1 := Finset.card_sdiff_add_card_eq_card hsub
  have h2 := Finset.card_le_card hdiff
  rw [abs_of_nonneg (by
    have := Finset.card_le_card hsub; rw [sub_nonneg]; exact_mod_cast this)]
  have : ((I.filter fun i => e i ⊆ insert a W).card : ℝ) =
      ((I.filter fun i => e i ⊆ insert a W) \ (I.filter fun i => e i ⊆ W)).card +
      (I.filter fun i => e i ⊆ W).card := by exact_mod_cast h1.symm
  rw [this]
  have : (((I.filter fun i => e i ⊆ insert a W) \ (I.filter fun i => e i ⊆ W)).card : ℝ) ≤
      (I.filter fun i => a ∈ e i).card := by exact_mod_cast h2
  linarith

/-- **Concentration of a containment count** (the full finite process). -/
theorem count_tail [Fintype V] (hq0 : 0 < q) (hq1 : q ≤ 1) {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (e : ι → Finset V) {r : ℕ} (hr : 0 < r) (her : ∀ i ∈ I, (e i).card ≤ r)
    {Δ : ℝ} (hΔ : 0 < Δ) (hdeg : ∀ a : V, ((I.filter fun i => a ∈ e i).card : ℝ) ≤ Δ)
    {L : ℝ} (hL : L ≤ I.card) :
    bprob q univ (fun W => (ccount I e W : ℝ) < L * q ^ r / 2) ≤
      Real.exp (-(L * q ^ (2 * r) / (16 * Δ * r))) := by
  set c : V → ℝ := fun a => (I.filter fun i => a ∈ e i).card
  set l : ℝ := q ^ r / (4 * Δ * r)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqr : 0 < q ^ r := pow_pos hq0 r
  have hqr1 : q ^ r ≤ 1 := pow_le_one₀ hq0.le hq1
  have hl : 0 ≤ l := by positivity
  have hlc : ∀ a ∈ (univ : Finset V), l * c a ≤ 1 := by
    intro a _
    calc l * c a ≤ l * Δ := mul_le_mul_of_nonneg_left (hdeg a) hl
      _ = q ^ r / (4 * r) := by simp only [l]; field_simp
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (1 : ℝ) ≤ r := by exact_mod_cast hr
        linarith
  set f : Finset V → ℝ := fun W => ccount I e W
  have hf : ∀ W ⊆ (univ : Finset V), ∀ a ∈ (univ : Finset V), a ∉ W →
      |f (insert a W) - f W| ≤ c a := fun W _ a _ _ => ccount_diff I e W a
  -- mean
  have hmean : (I.card : ℝ) * q ^ r ≤ bexp q univ f := by
    have : f = fun W => ∑ i ∈ I, (if e i ⊆ W then (1 : ℝ) else 0) := by
      ext W; simp only [f, ccount]; rw [Finset.sum_boole]
    rw [this, bexp_sum, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum; intro i hi
    rw [bexp_subset_ind univ (e i) (Finset.subset_univ _)]
    exact pow_le_pow_of_le_one hq0.le hq1 (her i hi)
  -- Σ c² ≤ Δ r |I|
  have hsum : ∑ a ∈ (univ : Finset V), c a ^ 2 ≤ Δ * r * I.card := by
    have h1 : ∑ a ∈ (univ : Finset V), c a ^ 2 ≤ ∑ a ∈ (univ : Finset V), Δ * c a := by
      apply Finset.sum_le_sum; intro a _
      have : 0 ≤ c a := Nat.cast_nonneg _
      rw [sq]; exact mul_le_mul_of_nonneg_right (hdeg a) this
    have h2 : ∑ a ∈ (univ : Finset V), c a = ∑ i ∈ I, ((e i).card : ℝ) := by
      simp only [c]
      have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := (univ : Finset V)) (t := I) (r := fun a i => a ∈ e i)
      simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at this
      exact_mod_cast (this.trans (Finset.sum_congr rfl fun i _ => by
        congr 1; ext a; simp))
    have h3 : ∑ i ∈ I, ((e i).card : ℝ) ≤ r * I.card := by
      calc ∑ i ∈ I, ((e i).card : ℝ) ≤ ∑ _i ∈ I, (r : ℝ) :=
            Finset.sum_le_sum fun i hi => by exact_mod_cast her i hi
        _ = r * I.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [← Finset.mul_sum, h2] at h1
    calc _ ≤ Δ * ∑ i ∈ I, ((e i).card : ℝ) := h1
      _ ≤ Δ * (r * I.card) := mul_le_mul_of_nonneg_left h3 hΔ.le
      _ = Δ * r * I.card := by ring
  set s : ℝ := I.card * q ^ r / 2
  have ht := tail_lower hq0.le hq1 c hl univ f hf hlc s
  have hI0 : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
  calc bprob q univ (fun W => (ccount I e W : ℝ) < L * q ^ r / 2)
      ≤ bprob q univ (fun W => f W ≤ bexp q univ f - s) := by
        unfold bprob; apply bexp_mono hq0.le hq1; intro W _
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso; apply h2
          have : L * q ^ r / 2 ≤ I.card * q ^ r / 2 := by
            have := mul_le_mul_of_nonneg_right hL hqr.le; linarith
          simp only [f, s]; linarith
        · norm_num
        · exact le_rfl
    _ ≤ Real.exp (-(l * s) + l ^ 2 * ∑ a ∈ univ, c a ^ 2) := ht
    _ ≤ Real.exp (-(I.card * q ^ (2 * r) / (16 * Δ * r))) := by
        apply Real.exp_le_exp.2
        have hl2 : l ^ 2 * ∑ a ∈ univ, c a ^ 2 ≤ l ^ 2 * (Δ * r * I.card) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg l)
        have e1 : l * s = I.card * q ^ (2 * r) / (8 * Δ * r) := by
          simp only [l, s]; rw [pow_mul']; field_simp; ring
        have e2 : l ^ 2 * (Δ * r * I.card) = I.card * q ^ (2 * r) / (16 * Δ * r) := by
          simp only [l]; rw [pow_mul']; field_simp; ring
        have e3 : (I.card : ℝ) * q ^ (2 * r) / (8 * Δ * r) =
            2 * ((I.card : ℝ) * q ^ (2 * r) / (16 * Δ * r)) := by field_simp; ring
        linarith
    _ ≤ Real.exp (-(L * q ^ (2 * r) / (16 * Δ * r))) := by
        apply Real.exp_le_exp.2
        have : L * q ^ (2 * r) ≤ I.card * q ^ (2 * r) :=
          mul_le_mul_of_nonneg_right hL (pow_pos hq0 _).le
        have hpos : 0 < 16 * Δ * r := by positivity
        have := div_le_div_of_nonneg_right this hpos.le
        linarith

end S07V24
