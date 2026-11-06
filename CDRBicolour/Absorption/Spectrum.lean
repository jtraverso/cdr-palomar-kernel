/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.MainPaperIIITriangleMonitors
public import CDRBicolour.Absorption.AACCount
public import CDRBicolour.Absorption.SeedCounts
public import CDRBicolour.Absorption.Lattice
public import CDRBicolour.Absorption.Hinge

/-!
# Approximate spectrum of `AAC` blocks (backlog item 3, approximate sufficiency)

Theorem T+ of Paper III with one triangle monitor (the indicator of the type `AAC`) applied to
the seed family `wtS s`, `|s| ≤ 1/32`: for every `η > 0` and every sufficiently large admissible
profile, each target value `(1/2 - σ_A - s) · C(a,2)` is attained by the number of `AAC` blocks
of some realisation, up to `η n²`.  The targets fill an interval of length `C(a,2)/16`.
No external hypothesis is used.
-/

@[expose] public section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.BlockTypes

/-- **Approximate `AAC` spectrum.** -/
theorem cdr_aac_spectrum (η : ℝ) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c → ∀ s : ℝ, |s| ≤ 1 / 32 →
      ∃ S : STS (Fin (a + b + c)), IsStrictBicolouring S (col3 a b c) ∧
        classSize (col3 a b c) 0 = a ∧ classSize (col3 a b c) 1 = b ∧
        classSize (col3 a b c) 2 = c ∧
        |(typeCount S (col3 a b c) 0 2 : ℝ) - (1 / 2 - sigA a c - s) * (a.choose 2 : ℝ)| ≤
          η * ((a + b + c : ℕ) : ℝ) ^ 2 := by
  obtain ⟨n₀, hT⟩ := Vortex.main_theorem_T_with_triangle_monitors cdrF (1 / 32) 8 η 6 0
    (by norm_num) (by norm_num) le_rfl hη
  refine ⟨max n₀ 400, fun a b c h hn s hs => ?_⟩
  have h400 : 400 ≤ a + b + c := le_of_max_le_right hn
  obtain ⟨D, hD, hmon⟩ := hT (cdrHost a b c) (fun T => wtS a b c s (T.val.map (col3 a b c)))
    (by rw [Fintype.card_fin]; exact le_of_max_le_left hn) (cdr_H1_family h h400 hs)
    (cdr_H2 h h400) (cdr_H3' h h400) (cdr_H4 h h400) Unit
    (fun _ Q => if Q.val.map (col3 a b c) = aac then 1 else 0)
    (by simp) (fun _ Q _ => by split_ifs <;> simp)
  obtain ⟨S, hSD, hcol, ha, hb, hc⟩ := sts_of_decomposition D hD
  refine ⟨S, hcol, ha, hb, hc, ?_⟩
  have hm := hmon ()
  rw [seed_aac_total h s] at hm
  rw [typeCount_aac, hSD]
  simpa [Fintype.card_fin] using hm

/-- **Dense `AAC` spectrum on the whole necessary interval.**  For every `ε > 0` and every
sufficiently large admissible profile: every `t` for which the six block-type counts forced by
`N_AAC = t` are all at least `ε n²` is the number of `AAC` blocks of some realisation, up to
`ε n²`.  (By `realised_type_identities`, the counts of any realisation are these six affine
functions of its `N_AAC`, and they are `≥ 0`; so this covers the necessary interval up to
margins `ε n²`.) -/
theorem cdr_aac_dense (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c → ∀ t : ℝ,
      (let N := ((a + b + c : ℕ) : ℝ); ε * N ^ 2 ≤ cntAAB a b c t ∧ ε * N ^ 2 ≤ cntAAC a b c t ∧
        ε * N ^ 2 ≤ cntBBC a b c t ∧ ε * N ^ 2 ≤ cntABB a b c t ∧
        ε * N ^ 2 ≤ cntACC a b c t ∧ ε * N ^ 2 ≤ cntBCC a b c t) →
      ∃ S : STS (Fin (a + b + c)), IsStrictBicolouring S (col3 a b c) ∧
        classSize (col3 a b c) 0 = a ∧ classSize (col3 a b c) 1 = b ∧
        classSize (col3 a b c) 2 = c ∧
        |(typeCount S (col3 a b c) 0 2 : ℝ) - t| ≤ ε * ((a + b + c : ℕ) : ℝ) ^ 2 := by
  obtain ⟨n₀, hT⟩ := Vortex.main_theorem_T_with_triangle_monitors cdrF (1 / 32) (64 + 1 / ε) ε 6 0
    (by norm_num) (le_add_of_le_of_nonneg (by norm_num) (by positivity)) le_rfl hε
  refine ⟨max n₀ 400, fun a b c h hn t ht => ?_⟩
  have h400 : 400 ≤ a + b + c := le_of_max_le_right hn
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
  obtain ⟨D, hD, hmon⟩ := hT (cdrHost a b c) (fun T => wtN a b c t (T.val.map (col3 a b c)))
    (by rw [Fintype.card_fin]; exact le_of_max_le_left hn)
    (cdr_H1_counts h h400 hε h1 h2 h3 h4 h5 h6)
    (cdr_H2 h h400) (cdr_H3' h h400) (cdr_H4 h h400) Unit
    (fun _ Q => if Q.val.map (col3 a b c) = aac then 1 else 0)
    (by simp) (fun _ Q _ => by split_ifs <;> simp)
  obtain ⟨S, hSD, hcol, ha, hb, hc⟩ := sts_of_decomposition D hD
  refine ⟨S, hcol, ha, hb, hc, ?_⟩
  have hm := hmon ()
  rw [seedN_aac_total h h400 t] at hm
  rw [typeCount_aac, hSD]
  simpa [Fintype.card_fin] using hm

/-- `C(a,2) ≥ n²/32` when `a + b + c + 8 ≤ 4a`. -/
theorem choose_two_ge {a n : ℕ} (ha : n + 8 ≤ 4 * a) : ((n : ℝ) ^ 2) / 32 ≤ (a.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two]
  have : ((n : ℝ) + 8) ≤ 4 * a := by exact_mod_cast ha
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-- **Many realisations with distinct `AAC` counts.**  For every `K`, every sufficiently large
admissible profile has `K` realisations whose numbers of `AAC` blocks are pairwise distinct;
in particular they are pairwise non-isomorphic as coloured systems. -/
theorem cdr_many_aac_counts (K : ℕ) :
    ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
      ∃ S : Fin K → STS (Fin (a + b + c)),
        (∀ i, IsStrictBicolouring (S i) (col3 a b c) ∧ classSize (col3 a b c) 0 = a ∧
          classSize (col3 a b c) 1 = b ∧ classSize (col3 a b c) 2 = c) ∧
        Function.Injective fun i => typeCount (S i) (col3 a b c) 0 2 := by
  have hK : (0 : ℝ) < 4096 * (K + 1) := by positivity
  obtain ⟨n₀, hsp⟩ := cdr_aac_spectrum (1 / (4096 * (K + 1))) (by positivity)
  refine ⟨max n₀ 400, fun a b c h hn => ?_⟩
  have h400 : 400 ≤ a + b + c := le_of_max_le_right hn
  let s : Fin K → ℝ := fun i => (i : ℝ) / (32 * (K + 1))
  have hs : ∀ i, |s i| ≤ 1 / 32 := by
    intro i
    have hi : (i : ℝ) ≤ K := by exact_mod_cast i.isLt.le
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  choose S hS using fun i => hsp a b c h (le_of_max_le_left hn) (s i) (hs i)
  refine ⟨S, fun i => ⟨(hS i).1, (hS i).2.1, (hS i).2.2.1, (hS i).2.2.2.1⟩, ?_⟩
  intro i j hij
  by_contra hne
  have hne' : (i : ℝ) ≠ j := by exact_mod_cast Fin.val_ne_of_ne hne
  have hi := (hS i).2.2.2.2
  have hj := (hS j).2.2.2.2
  simp only at hij
  rw [hij] at hi
  obtain ⟨ha4, -, -⟩ := class_lower_all h h400
  have hC := choose_two_ge ha4
  set N : ℝ := ((a + b + c : ℕ) : ℝ)
  set A : ℝ := (a.choose 2 : ℝ)
  have hN : 0 < N := by positivity
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  -- the two targets differ by `|i - j| · A / (32 (K+1)) ≥ A / (32 (K+1))`
  have hdiff : A / (32 * (K + 1)) ≤ |(1 / 2 - sigA a c - s i) * A - (1 / 2 - sigA a c - s j) * A| := by
    have : (1 / 2 - sigA a c - s i) * A - (1 / 2 - sigA a c - s j) * A =
        ((j : ℝ) - i) * (A / (32 * (K + 1))) := by
      simp only [s]; field_simp; ring
    rw [this, abs_mul, abs_of_nonneg (div_nonneg hA0 (by positivity))]
    have h1 : (1 : ℝ) ≤ |(j : ℝ) - i| := by
      rcases lt_or_gt_of_ne hne' with hlt | hlt
      · have : (i : ℕ) + 1 ≤ j := by exact_mod_cast hlt
        rw [abs_of_nonneg (by linarith)]
        have : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast this
        linarith
      · have : (j : ℕ) + 1 ≤ i := by exact_mod_cast hlt
        rw [abs_of_nonpos (by linarith)]
        have : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast this
        linarith
    nlinarith [div_nonneg hA0 (show (0 : ℝ) ≤ 32 * (K + 1) by positivity)]
  have htri := abs_sub_le ((1 / 2 - sigA a c - s i) * A)
    (typeCount (S j) (col3 a b c) 0 2 : ℝ) ((1 / 2 - sigA a c - s j) * A)
  have hi' : |(1 / 2 - sigA a c - s i) * A - (typeCount (S j) (col3 a b c) 0 2 : ℝ)| ≤
      1 / (4096 * (K + 1)) * N ^ 2 := by rw [abs_sub_comm]; exact hi
  have hsum : A / (32 * (K + 1)) ≤ 2 * (1 / (4096 * (K + 1)) * N ^ 2) := by linarith
  have hA : N ^ 2 / 32 ≤ A := hC
  rw [div_le_iff₀ (by positivity)] at hsum
  have : 2 * (1 / (4096 * (K + 1)) * N ^ 2) * (32 * (K + 1)) = N ^ 2 / 64 := by
    field_simp; ring
  rw [this] at hsum
  nlinarith

end CDRBicolour.Absorption
