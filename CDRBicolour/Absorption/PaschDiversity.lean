/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.MainPaperIIIPasch
public import CDRBicolour.Absorption.PaschFamily
public import CDRBicolour.Absorption.AACCount
public import CDRBicolour.Absorption.Lattice
public import CDRBicolour.Absorption.Hinge

/-!
# Many realisations with distinct Pasch counts (backlog item 1)

For every `K`, every sufficiently large admissible profile is realised by `K` strictly
bicoloured STS with pairwise distinct numbers of Pasch configurations; in particular they are
pairwise non-isomorphic as STS.

Proof.  The Pasch target `F(t)` of the seed `μ_t = μ₀ + t δ / n` is even
(`target_even`), hence `F(t) = F(0) + A₂ t² + A₄ t⁴` with
`A₄ = n⁻⁴ ∑_S ∏_{T∈S} δ T ≥ m⁶ / n⁴ ≥ n² / 40⁶` (`family_bound`).  On `2K+1` grid values of
`s = t²` the quadratic `A₀ + A₂ s + A₄ s²` has `K` pairwise `A₄ g²`-separated values
(`separated_values`).  Theorem T+ with Pasch control (Paper III) realises each seed with Pasch
count within `η n²` of its target, and `η` is chosen with `2 η n² < A₄ g²`.
-/

@[expose] public section

namespace CDRBicolour.Absorption.PaschSeed

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.PaschTools

theorem target_eq_sum {X : Type} [Fintype X] [DecidableEq X] (μ : Finset X → ℝ)
    (D : Finset (Finset X)) :
    Pasch.target μ D = ∑ S ∈ Pasch.configurations D, ∏ T ∈ S, μ T := by
  rw [Pasch.target, Pasch.statistic_eq_sum]

set_option maxHeartbeats 1600000 in
/-- **Many realisations with pairwise distinct Pasch counts.** -/
theorem cdr_many_pasch_counts (K : ℕ) :
    ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
      ∃ S : Fin K → STS (Fin (a + b + c)),
        (∀ i, IsStrictBicolouring (S i) (col3 a b c) ∧ classSize (col3 a b c) 0 = a ∧
          classSize (col3 a b c) 1 = b ∧ classSize (col3 a b c) 2 = c) ∧
        Function.Injective fun i => Pasch.count (S i).blocks := by
  set g : ℝ := 1 / (64 * (2 * K + 1)) with hg_def
  have hg : 0 < g := by positivity
  set κ : ℝ := 1 / 40 ^ 6 with hκ_def
  set η : ℝ := κ * g ^ 2 / 3 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨n₀, hT⟩ := Vortex.main_theorem_T_with_triangle_monitors_and_pasch cdrF (1 / 32) 8 η 6 0
    (by norm_num) (by norm_num) le_rfl hη
  refine ⟨max n₀ 400, fun a b c h hn => ?_⟩
  have h400 : 400 ≤ a + b + c := le_of_max_le_right hn
  obtain ⟨ha4, hb4, -⟩ := class_lower_all h h400
  set m := min a b / 8 with hm_def
  have hmin : a + b + c + 8 ≤ 4 * min a b := by
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab]; exact ha4
    · rw [min_eq_right hab]; exact hb4
  have H : Hyp a b m := ⟨by omega, by omega, by omega⟩
  set N : ℝ := ((a + b + c : ℕ) : ℝ) with hN_def
  have hN0 : 0 < N := by positivity
  have hmN : N ≤ 40 * m := by
    have : a + b + c ≤ 40 * m := by omega
    simp only [hN_def]; exact_mod_cast this
  set C := Pasch.configurations (allowed (cdrHost a b c) cdrF) with hC_def
  have hC : ∀ S ∈ C, #S = 4 := fun S hS => ((Pasch.mem_configurations).mp hS).2.1
  set x : Finset (Fin (a + b + c)) → ℝ := fun T => wt a b c (T.val.map (col3 a b c)) with hx_def
  set y : Finset (Fin (a + b + c)) → ℝ := fun T => δ a m T / N with hy_def
  obtain ⟨A₂, hA⟩ := even_quartic C hC x y (target_even H)
  set A₀ := ∑ S ∈ C, ∏ T ∈ S, (x T + 0 * y T) with hA₀_def
  set A₄ := ∑ S ∈ C, ∏ T ∈ S, y T with hA₄_def
  -- the leading coefficient
  have hA₄ : N ^ 2 * κ ≤ A₄ := by
    have e : A₄ = (∑ S ∈ C, ∏ T ∈ S, δ a m T) / N ^ 4 := by
      simp only [hA₄_def, hy_def, sum_div]
      refine sum_congr rfl fun S hS => ?_
      rw [prod_div_distrib, prod_const, hC S hS]
    rw [e, le_div_iff₀ (by positivity)]
    have hf := family_bound (c := c) H
    have h6 : N ^ 6 * κ ≤ (m : ℝ) ^ 6 := by
      have h40 : N / 40 ≤ m := by linarith
      have := pow_le_pow_left₀ (by positivity) h40 6
      rw [div_pow] at this
      calc N ^ 6 * κ = N ^ 6 / 40 ^ 6 := by rw [hκ_def]; ring
        _ ≤ _ := this
    have : N ^ 2 * κ * N ^ 4 = N ^ 6 * κ := by ring
    rw [this]
    linarith
  have hA₄pos : 0 < A₄ := lt_of_lt_of_le (by positivity) hA₄
  obtain ⟨s, hsr, hsep⟩ := separated_values A₀ A₂ A₄ g hA₄pos hg K
  -- each grid value is realised
  have hreal : ∀ i : Fin K, ∃ S : STS (Fin (a + b + c)),
      (IsStrictBicolouring S (col3 a b c) ∧ classSize (col3 a b c) 0 = a ∧
        classSize (col3 a b c) 1 = b ∧ classSize (col3 a b c) 2 = c) ∧
      |(Pasch.count S.blocks : ℝ) - (A₀ + A₂ * s i + A₄ * s i ^ 2)| ≤ η * N ^ 2 := by
    intro i
    set t := Real.sqrt (s i) with ht_def
    have ht2 : t ^ 2 = s i := Real.sq_sqrt (hsr i).1
    have ht : |t| ≤ 1 / 8 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [show (1 / 8 : ℝ) = Real.sqrt (1 / 64) by
        rw [show (1 / 64 : ℝ) = (1 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt
      have := (hsr i).2
      have hK : (2 * K * g : ℝ) ≤ 1 / 64 := by
        rw [hg_def, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    obtain ⟨D, hD, -, hP⟩ := hT (cdrHost a b c) (μt a b c m t)
      (by rw [Fintype.card_fin]; exact le_of_max_le_left hn) (pasch_seed_H1 H h h400 ht)
      (cdr_H2 h h400) (cdr_H3' h h400) (cdr_H4 h h400) Empty (fun e => e.elim)
      (by simp) (fun e => e.elim)
    obtain ⟨S, hSD, hcol, ha, hb, hc⟩ := sts_of_decomposition D hD
    refine ⟨S, ⟨hcol, ha, hb, hc⟩, ?_⟩
    rw [hSD]
    have htarget : Pasch.target (μt a b c m t) (allowed (cdrHost a b c) cdrF) =
        A₀ + A₂ * s i + A₄ * s i ^ 2 := by
      rw [target_eq_sum]
      have := hA t
      simp only [μt]
      rw [this, ← ht2]
      ring
    rw [← htarget]
    rw [Fintype.card_fin] at hP
    convert hP using 3
    all_goals congr!
  choose S hS using hreal
  refine ⟨S, fun i => (hS i).1, fun i j hij => ?_⟩
  by_contra hne
  have h1 := (hS i).2
  have h2 := (hS j).2
  simp only at hij
  rw [hij] at h1
  have hs := hsep i j hne
  have htri := abs_sub_le (A₀ + A₂ * s i + A₄ * s i ^ 2) (Pasch.count (S j).blocks : ℝ)
    (A₀ + A₂ * s j + A₄ * s j ^ 2)
  rw [abs_sub_comm] at h1
  have h3 : N ^ 2 * κ * g ^ 2 ≤ A₄ * g ^ 2 := mul_le_mul_of_nonneg_right hA₄ (by positivity)
  have h4 : 2 * (η * N ^ 2) < N ^ 2 * κ * g ^ 2 := by
    have e : 2 * (η * N ^ 2) = 2 / 3 * (N ^ 2 * κ * g ^ 2) := by rw [hη_def]; ring
    have : 0 < N ^ 2 * κ * g ^ 2 := by positivity
    rw [e]; linarith
  linarith

/-- **Many pairwise non-isomorphic realisations.**  For every `K`, every sufficiently large
admissible profile is realised by `K` strictly bicoloured STS no two of which are isomorphic
as STS (no relabelling of the points maps the blocks of one onto the blocks of the other). -/
theorem cdr_many_nonisomorphic (K : ℕ) :
    ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
      ∃ S : Fin K → STS (Fin (a + b + c)),
        (∀ i, IsStrictBicolouring (S i) (col3 a b c) ∧ classSize (col3 a b c) 0 = a ∧
          classSize (col3 a b c) 1 = b ∧ classSize (col3 a b c) 2 = c) ∧
        ∀ i j, i ≠ j → ∀ e : Fin (a + b + c) ≃ Fin (a + b + c),
          (S j).blocks ≠ (S i).blocks.map (mapEmbedding e.toEmbedding).toEmbedding := by
  obtain ⟨n₀, h⟩ := cdr_many_pasch_counts K
  refine ⟨n₀, fun a b c ha hn => ?_⟩
  obtain ⟨S, hS, hinj⟩ := h a b c ha hn
  refine ⟨S, hS, fun i j hij e heq => hij (hinj ?_)⟩
  simp only
  rw [heq, count_map_equiv]

end CDRBicolour.Absorption.PaschSeed
