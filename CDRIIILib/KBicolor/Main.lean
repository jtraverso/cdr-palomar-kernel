/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.MainPaperIII
public import CDRIIILib.KBicolor.Lattice

/-!
# k-bicolourable Steiner triple systems via Paper III (Theorem T)

`kbicolour_eventually`: fix `k ≥ 2`, `0 < δ ≤ 1` and `η > 0`. There is `n₀` such that every
labelling `lab : Fin n → Fin k` with `n ≥ n₀` odd, every class of size at least `δ n`, all
products of two class sizes even, the divisibility identity `3 Σ_X c_X (c_X - 1) = n (n - 1)`
and seed data `a ≥ η` (`SeedData`) is the colour-class partition of a Steiner triple system all
of whose blocks meet exactly two classes: an allowed decomposition of all edges of the complete
graph with bicoloured types.

The proof is Theorem T of Paper III (`TypedTriangle.Vortex.main_theorem_T`) with
* H1 `kH1` (type-uniform seed, `C = 1/η + 2/δ`),
* H2 `physical_of` (direct lattice argument),
* H3 `kH3` (`α = δ/2`, weakened to `δ²/4`),
* H4 `kH4` (octahedral hinges, `α = δ²/4`, `h = 6`).
The threshold `n₀` comes from Theorem T and is not explicit.

For `k = 4` (resp. `5`) this answers Colbourn–Dinitz–Rosa, Conjecture 3.5 (resp. 3.6), for
every large order that admits a balanced split with seed data; the existence of such splits for
all large orders is an arithmetic statement (sums of three squares), not formalized here.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle

theorem commonNbr_mono {V I : Type*} [Fintype V] {H : Host V I} {F : Set (Multiset I)}
    {α β : ℝ} (h : CommonNbrCond H F β) (hαβ : α ≤ β) : CommonNbrCond H F α := by
  intro u v huv X hX
  have := h u v huv X hX
  have : α * Fintype.card V ≤ β * Fintype.card V :=
    mul_le_mul_of_nonneg_right hαβ (by positivity)
  linarith

/-- The divisibility identity gives the pair identity used for H2. -/
theorem pair_of_div {k n : ℕ} (c : Fin k → ℕ) (hsum : ∑ X, c X = n)
    (hdiv : 3 * ∑ X, c X * (c X - 1) = n * (n - 1)) :
    ∑ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2), c j.1 * c j.2 =
      ∑ X, c X * (c X - 1) := by
  have hsq : n * n = ∑ X, c X * c X +
      ∑ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2), (c j.1 * c j.2 + c j.2 * c j.1) := by
    rw [← sum_pairs (fun X Y => c X * c Y), ← hsum, sum_mul_sum, Fintype.sum_prod_type]
  have hsym : ∑ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2), (c j.1 * c j.2 + c j.2 * c j.1)
      = 2 * ∑ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2), c j.1 * c j.2 := by
    rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  have hcc : ∑ X, c X * c X = ∑ X, c X * (c X - 1) + n := by
    rw [← hsum, ← sum_add_distrib]
    refine sum_congr rfl fun X _ => ?_
    rcases Nat.eq_zero_or_pos (c X) with h0 | hpos
    · rw [h0]
    · have : c X * (c X - 1) + c X = c X * c X := by
        rw [Nat.mul_sub, mul_one, Nat.sub_add_cancel (Nat.le_mul_self _)]
      exact this.symm
  rw [hsym, hcc] at hsq
  set S := ∑ X, c X * (c X - 1)
  set P := ∑ j ∈ univ.filter (fun j : Fin k × Fin k => j.1 < j.2), c j.1 * c j.2
  have hn1 : n * (n - 1) + n = n * n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]
    · rw [Nat.mul_sub, mul_one, Nat.sub_add_cancel (Nat.le_mul_self _)]
  omega

/-- **k-bicolourings, asymptotically.** -/
theorem kbicolour_eventually (k : ℕ) (hk : 2 ≤ k) {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ X, δ * n ≤ ksz lab X) →
      (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X - 1) = n * (n - 1) →
      (∃ a, SeedData (ksz lab) η a) →
      ∃ D : Finset (Finset (Fin n)), IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D := by
  have hC : (1 : ℝ) ≤ 1 / η + 2 / δ := by
    have : 2 ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
    have : 0 < 1 / η := by positivity
    linarith
  obtain ⟨N, hT⟩ := Vortex.main_theorem_T (bicF k) (δ ^ 2 / 4) (1 / η + 2 / δ) 6
    (by positivity) hC le_rfl
  refine ⟨max N (Nat.ceil (10 / δ)), fun n lab hn hodd hcls heven hdiv ⟨a, ha⟩ => ?_⟩
  have hcard : (Fintype.card (Fin n) : ℝ) = n := by simp
  have h10 : 10 ≤ δ * (Fintype.card (Fin n) : ℝ) := by
    rw [hcard]
    have : (Nat.ceil (10 / δ) : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
    have := (div_le_iff₀ hδ).1 ((Nat.le_ceil _).trans this)
    linarith
  have hcls' : ∀ X, δ * (Fintype.card (Fin n) : ℝ) ≤ ksz lab X := by
    intro X; rw [hcard]; exact hcls X
  -- H1
  have H1 := kH1 lab hη hδ ha hcls' (by linarith)
  -- H3
  have H3 := commonNbr_mono (kH3 lab hcls' (by linarith))
    (by nlinarith : δ ^ 2 / 4 ≤ δ / 2)
  -- H4
  have H4 := kH4 lab hδ hcls' h10
  -- H2
  have hbig : Big lab := by
    intro X u v
    set S := univ.filter fun w : Fin n => lab w = X with hS
    have h3 : 3 ≤ S.card := by
      have : (3 : ℝ) ≤ S.card := by have := hcls' X; unfold ksz at this; linarith
      exact_mod_cast this
    have h1 := pred_card_le_card_erase (s := S.erase u) (a := v)
    have h2 := pred_card_le_card_erase (s := S) (a := u)
    obtain ⟨w, hw⟩ : ((S.erase u).erase v).Nonempty := by
      rw [← card_pos]; omega
    simp only [mem_erase, hS, mem_filter, mem_univ, true_and] at hw
    exact ⟨w, hw.2.2, hw.2.1, hw.1⟩
  have hnpos : 0 < n := by obtain ⟨m, hm⟩ := hodd; omega
  have hex : ∀ X : Fin k, ∃ v, lab v = X := fun X => by
    obtain ⟨w, hw, -⟩ := hbig X ⟨0, hnpos⟩ ⟨0, hnpos⟩
    · exact ⟨w, hw⟩
  choose o ho using hex
  let nx : Fin k → Fin k := fun X => if X.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hnx : ∀ X, nx X ≠ X := by
    intro X h
    simp only [nx] at h
    split_ifs at h with h0
    · have := congrArg Fin.val h; simp at this; omega
    · have := congrArg Fin.val h; simp at this; omega
  have hsum : ∑ X, ksz lab X = n := by
    unfold ksz
    rw [← card_eq_sum_card_fiberwise (f := lab) (fun _ _ => mem_univ _), card_univ,
      Fintype.card_fin]
  have hn' : Even (Fintype.card (Fin n) - 1) := by
    rw [Fintype.card_fin]; obtain ⟨m, hm⟩ := hodd; exact ⟨m, by omega⟩
  have H2 := physical_of (lab := lab) hbig ho hnx ⟨0, by omega⟩ hn' heven
    (pair_of_div (ksz lab) hsum hdiv)
  exact hT (kHost lab) (by rw [Fintype.card_fin]; exact le_of_max_le_left hn) ⟨_, H1⟩ H2 H3 H4

end CDRBicolour.KBicolor
