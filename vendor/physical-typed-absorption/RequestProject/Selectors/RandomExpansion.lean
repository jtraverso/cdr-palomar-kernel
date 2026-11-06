/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Selectors.PermCount
public import RequestProject.Selectors.BalancedBound

@[expose] public section

/-!
# Small-set expansion of the 20-round permutation/injection construction (one direction)

`N = 4k` auxiliaries `A = Fin N` on one side, ports `P` (`|P| ≤ k`) embedded by
`e : P ↪ Fin N`.  A sample is a pair `(π, τ)` of `20`-tuples of permutations of `Fin N`;
in round `i` the auxiliary `a` is joined to `π i a` and the port `p` to `τ i (e p)`
(so the ports are joined by the injection `τ i ∘ e`, sampled uniformly).

`card_bad_le` : the number of samples for which some set `X ⊆ A ⊕ P` with `|X| ≤ M`
(`M = window k`) has fewer than `|X|` neighbours is at most `(N!)^40 / 3`, i.e. at most a
third of all samples.  Proof: an explicit union bound over `(X, T)`, `|T| = |X| - 1`,
sampling without replacement (`SelCount.permInto_mul_pow_le`) and `SelBound.sum_term_le`.
-/

namespace SelRandom

open Finset SelCount SelBound

/-- One side of a sample: `20` permutations. -/
abbrev Rounds (N : ℕ) := Fin 20 → Equiv.Perm (Fin N)

variable {N : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

/-- Image of a vertex of `A ⊕ P` in round `i`. -/
def img (e : P ↪ Fin N) (π τ : Rounds N) (i : Fin 20) : Fin N ⊕ P → Fin N :=
  Sum.elim (π i) (fun p => τ i (e p))

/-- Auxiliary neighbourhood of `X` in the sampled graph. -/
def nbr (e : P ↪ Fin N) (π τ : Rounds N) (X : Finset (Fin N ⊕ P)) : Finset (Fin N) :=
  univ.filter (fun b => ∃ x ∈ X, ∃ i, img e π τ i x = b)

/-- A sample is bad if some set of size `≤ M` does not expand. -/
def Bad (e : P ↪ Fin N) (M : ℕ) (ω : Rounds N × Rounds N) : Prop :=
  ∃ X : Finset (Fin N ⊕ P), X.card ≤ M ∧ (nbr e ω.1 ω.2 X).card < X.card

/-- Samples for which all neighbours of `X` lie in `T`. -/
def badXT (e : P ↪ Fin N) (X : Finset (Fin N ⊕ P)) (T : Finset (Fin N)) :
    Finset (Rounds N × Rounds N) :=
  (Fintype.piFinset fun _ => univ.filter (fun π : Equiv.Perm (Fin N) => ∀ y ∈ X.toLeft, π y ∈ T))
  ×ˢ (Fintype.piFinset fun _ =>
      univ.filter (fun τ : Equiv.Perm (Fin N) => ∀ y ∈ X.toRight.map e, τ y ∈ T))

lemma card_badXT (e : P ↪ Fin N) (X : Finset (Fin N ⊕ P)) (T : Finset (Fin N)) :
    (badXT e X T).card = permInto X.toLeft T ^ 20 * permInto (X.toRight.map e) T ^ 20 := by
  simp [badXT, card_product, Fintype.card_piFinset, permInto]

lemma permInto_le_real (hN : 0 < N) (Y T : Finset (Fin N)) :
    (permInto Y T : ℝ) ≤ (N.factorial : ℝ) * ((T.card : ℝ) / N) ^ Y.card := by
  have h := permInto_mul_pow_le Y T
  simp only [Fintype.card_fin] at h
  have hNR : (0 : ℝ) < (N : ℝ) ^ Y.card := by positivity
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ hNR]
  exact_mod_cast h

lemma card_badXT_le (hN : 0 < N) (e : P ↪ Fin N) (X : Finset (Fin N ⊕ P))
    (T : Finset (Fin N)) :
    ((badXT e X T).card : ℝ) ≤ (N.factorial : ℝ) ^ 40 * ((T.card : ℝ) / N) ^ (20 * X.card) := by
  rw [card_badXT]
  push_cast
  have h1 := permInto_le_real hN X.toLeft T
  have h2 := permInto_le_real hN (X.toRight.map e) T
  rw [card_map] at h2
  have hX : X.card = X.toLeft.card + X.toRight.card := card_toLeft_add_card_toRight.symm
  calc (permInto X.toLeft T : ℝ) ^ 20 * (permInto (X.toRight.map e) T : ℝ) ^ 20
      ≤ ((N.factorial : ℝ) * ((T.card : ℝ) / N) ^ X.toLeft.card) ^ 20 *
        ((N.factorial : ℝ) * ((T.card : ℝ) / N) ^ X.toRight.card) ^ 20 := by
        gcongr
    _ = (N.factorial : ℝ) ^ 40 * ((T.card : ℝ) / N) ^ (20 * X.card) := by
        rw [hX]; ring

omit [DecidableEq P] in
lemma bad_mem_badXT (e : P ↪ Fin N) (M : ℕ) (hMN : M ≤ N) (ω : Rounds N × Rounds N)
    (h : Bad e M ω) :
    ∃ s ∈ Icc 1 M, ∃ X ∈ powersetCard s (univ : Finset (Fin N ⊕ P)),
      ∃ T ∈ powersetCard (s - 1) (univ : Finset (Fin N)), ω ∈ badXT e X T := by
  obtain ⟨X, hXM, hlt⟩ := h
  obtain ⟨T, hT, hTc⟩ := Finset.exists_superset_card_eq (s := nbr e ω.1 ω.2 X)
    (n := X.card - 1) (by omega) (by simp; omega)
  refine ⟨X.card, mem_Icc.mpr ⟨by omega, hXM⟩, X, by simp, T, by simp [hTc], ?_⟩
  simp only [badXT, mem_product, Fintype.mem_piFinset, mem_filter, mem_univ, true_and]
  refine ⟨fun i y hy => hT ?_, fun i y hy => hT ?_⟩
  · simp only [nbr, mem_filter, mem_univ, true_and]
    exact ⟨Sum.inl y, mem_toLeft.mp hy, i, rfl⟩
  · simp only [nbr, mem_filter, mem_univ, true_and]
    obtain ⟨p, hp, rfl⟩ := mem_map.mp hy
    exact ⟨Sum.inr p, mem_toRight.mp hp, i, rfl⟩

open Classical in
/-- **Union bound.** At most a third of the samples are bad. -/
theorem card_bad_le (k : ℕ) (hk : 1 ≤ k) (hP : Fintype.card P ≤ k) (e : P ↪ Fin (4 * k)) :
    ((univ.filter (fun ω : Rounds (4 * k) × Rounds (4 * k) => Bad e (window k) ω)).card : ℝ)
      ≤ ((4 * k).factorial : ℝ) ^ 40 / 3 := by
  have hN : 0 < (4 * k) := by omega
  have hMN : window k ≤ (4 * k) := by unfold window; omega
  set U := (Icc 1 (window k)).biUnion (fun s =>
    (powersetCard s (univ : Finset (Fin (4 * k) ⊕ P))).biUnion (fun X =>
      (powersetCard (s - 1) (univ : Finset (Fin (4 * k)))).biUnion (fun T => badXT e X T)))
  have hsub : univ.filter (fun ω : Rounds (4 * k) × Rounds (4 * k) => Bad e (window k) ω) ⊆ U := by
    intro ω hω
    obtain ⟨s, hs, X, hX, T, hT, hωXT⟩ :=
      bad_mem_badXT e (window k) hMN ω (mem_filter.mp hω).2
    exact mem_biUnion.mpr ⟨s, hs, mem_biUnion.mpr ⟨X, hX, mem_biUnion.mpr ⟨T, hT, hωXT⟩⟩⟩
  have hcard : (univ.filter (fun ω : Rounds (4 * k) × Rounds (4 * k) => Bad e (window k) ω)).card ≤
      ∑ s ∈ Icc 1 (window k), ∑ X ∈ powersetCard s (univ : Finset (Fin (4 * k) ⊕ P)),
        ∑ T ∈ powersetCard (s - 1) (univ : Finset (Fin (4 * k))), (badXT e X T).card := by
    refine (card_le_card hsub).trans ?_
    refine card_biUnion_le.trans (sum_le_sum fun s _ => ?_)
    refine card_biUnion_le.trans (sum_le_sum fun X _ => ?_)
    exact card_biUnion_le
  have hreal : ((univ.filter (fun ω : Rounds (4 * k) × Rounds (4 * k) => Bad e (window k) ω)).card : ℝ) ≤
      ∑ s ∈ Icc 1 (window k), ((4 * k).factorial : ℝ) ^ 40 *
        ((((4 * k) + Fintype.card P).choose s : ℝ) * ((4 * k).choose (s - 1) : ℝ) *
          (((s - 1 : ℕ) : ℝ) / (4 * k)) ^ (20 * s)) := by
    refine (Nat.cast_le.mpr hcard).trans ?_
    push_cast
    refine sum_le_sum fun s _ => ?_
    calc ∑ X ∈ powersetCard s (univ : Finset (Fin (4 * k) ⊕ P)),
          ∑ T ∈ powersetCard (s - 1) (univ : Finset (Fin (4 * k))), ((badXT e X T).card : ℝ)
        ≤ ∑ X ∈ powersetCard s (univ : Finset (Fin (4 * k) ⊕ P)),
          ∑ T ∈ powersetCard (s - 1) (univ : Finset (Fin (4 * k))),
            ((4 * k).factorial : ℝ) ^ 40 * (((s - 1 : ℕ) : ℝ) / (4 * k)) ^ (20 * s) := by
          refine sum_le_sum fun X hX => sum_le_sum fun T hT => ?_
          have := card_badXT_le hN e X T
          rw [(mem_powersetCard.mp hT).2, (mem_powersetCard.mp hX).2] at this
          push_cast at this
          exact this
      _ = ((4 * k).factorial : ℝ) ^ 40 *
          ((((4 * k) + Fintype.card P).choose s : ℝ) * ((4 * k).choose (s - 1) : ℝ) *
            (((s - 1 : ℕ) : ℝ) / (4 * k)) ^ (20 * s)) := by
          rw [sum_const, sum_const, card_powersetCard, card_powersetCard, card_univ,
            card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
          ring
  refine hreal.trans ?_
  rw [← mul_sum]
  have hb := sum_term_le k (Fintype.card P) hk hP
  have hf : (0 : ℝ) ≤ ((4 * k).factorial : ℝ) ^ 40 := by positivity
  calc ((4 * k).factorial : ℝ) ^ 40 * ∑ s ∈ Icc 1 (window k),
        ((((4 * k) + Fintype.card P).choose s : ℝ) * ((4 * k).choose (s - 1) : ℝ) *
          (((s - 1 : ℕ) : ℝ) / (4 * k)) ^ (20 * s))
      ≤ ((4 * k).factorial : ℝ) ^ 40 * (1 / 3) := mul_le_mul_of_nonneg_left hb hf
    _ = ((4 * k).factorial : ℝ) ^ 40 / 3 := by ring

end SelRandom
