/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.StageB
public import CDRBicolour.Prefix.Prefix
public import CDRBicolour.L183.P2
public import CDRBicolour.L184.Assembly

/-!
# The P2 route, end to end

For `k ≥ 4` the profile `(12k²+14k+4, 12k²+14k+6, 12k²+20k+9)` is realised, assuming exactly
the two L181 completion statements and the two external edge-colouring theorems (CCJS Theorem 1.2,
Chetwynd–Hilton 1985 via Plantholt 2004 Thm 1.2), all stated as literal `Prop`s:

* stage A + stage B (L182) give the prefix data, `prefix_cover` the prefix blocks;
* the residual graph `F` on `C` has degrees `6k+2` (at `w`), `a-2` (on the `r = 3k+1` high labels)
  and `a` elsewhere, so L183 colours it with `a` colours;
* L184 assembles the STS.
-/

@[expose] public section

namespace CDRBicolour.Prefix

open Finset LeanPool.Vizing LeanPool.Vizing.ColourClasses CDRBicolour.L184 CDRBicolour.L183

/-- **P2 route.** -/
theorem P2_realises (hNA : L181_NoAnchor.{0}) (hS : L181_Star.{0})
    (k : ℕ) (hk : 4 ≤ k) :
    Realises (pa k) (pb k) (pc k) := by
  classical
  have hk2 : 16 ≤ k ^ 2 := by nlinarith
  have hcA : Fintype.card (AType (colP k)) = 12 * k ^ 2 + 14 * k + 4 := card_classA
  have hcC : Fintype.card (CType (colP k)) = 12 * k ^ 2 + 20 * k + 9 := card_classC
  -- stages A and B
  obtain ⟨μ, hμ, hμ', χA, MA, hχA, hMA, hMAd, htwo, hcnt⟩ :=
    stageA hNA (pa k) (pb k) (pc k) rfl (by nlinarith) ⟨6 * k ^ 2 + 7 * k + 2, by ring⟩
  obtain ⟨w, χB, MB, hχB, havoid, hMB, hMBd, hmB, hcntB⟩ :=
    stageB hS k (by omega) μ χA MA hMA hMAd htwo hcnt
  let d : PrefixData (colP k) := ⟨μ, χA, MA, χB, MB⟩
  have hv : d.Valid := ⟨hμ, hμ', hχA, hMA, hMAd, hχB, hMB, hMBd⟩
  obtain ⟨hP3, hPbic, hPres, hPcov⟩ := prefix_cover hv
  -- degrees of the residual graph
  set F : SimpleGraph (CType (colP k)) := resid MB with hF
  have hdeg : ∀ v, F.degree v + mult (GB MA) χB v = 12 * k ^ 2 + 20 * k + 8 := by
    intro v; have := resid_degree_add_mult hv v; rw [hcC] at this; exact this
  have hmw : mult (GB MA) χB w = 12 * k ^ 2 + 14 * k + 6 := by
    have h := mult_add_two_mul_class hχB w
    have h0 : (colourClass (GB MA).edgeFinset χB w).card = 0 := by
      rw [card_eq_zero]; ext x
      simp only [mem_colourClass, notMem_empty, iff_false, not_and]
      intro hx; exact havoid x hx
    rw [h0, card_classB] at h; simpa using h
  set P := univ.filter fun v => v ≠ w ∧ mult (GB MA) χB v = 6 * k + 6 with hP
  have hdw : F.degree w = 6 * k + 2 := by have := hdeg w; rw [hmw] at this; omega
  have hwP : w ∉ P := by simp [hP]
  have hdP : ∀ v ∈ P, F.degree v = 12 * k ^ 2 + 14 * k + 2 := by
    intro v hvP; simp only [hP, mem_filter, mem_univ, true_and] at hvP
    have := hdeg v; rw [hvP.2] at this; omega
  have hdR : ∀ v, v ≠ w → v ∉ P → F.degree v = 12 * k ^ 2 + 14 * k + 4 := by
    intro v hvw hvP
    simp only [hP, mem_filter, mem_univ, true_and, not_and] at hvP
    have := hdeg v
    rcases hmB v hvw with h | h
    · rw [h] at this; omega
    · exact absurd h (hvP hvw)
  have hPs : 2 * P.card = 6 * k + 2 := by rw [hP, hcntB]; ring
  -- L183: `F` is `a`-edge-colourable
  have hEC := l183_P2 k hk F w P hcC hdw hwP hdP hdR hPs
  have hEC' : EdgeColourable F (Fintype.card (AType (colP k))) := by rw [hcA]; exact hEC
  obtain ⟨colour, hproper⟩ := exists_properOn_of_edgeColourable F (by rw [hcA]; omega) hEC'
  -- the arithmetic hypotheses of L184
  have hodd : Odd (Fintype.card (CType (colP k))) := by
    rw [hcC]; exact ⟨6 * k ^ 2 + 10 * k + 4, by ring⟩
  have hpt : ∀ v, F.degree v + (2 * (if v ∈ P then 1 else 0) +
      (if v = w then 12 * k ^ 2 + 8 * k + 2 else 0)) = 12 * k ^ 2 + 14 * k + 4 := by
    intro v
    by_cases hvw : v = w
    · subst hvw; rw [if_neg hwP, if_pos rfl, hdw]; omega
    · by_cases hvP : v ∈ P
      · rw [if_pos hvP, if_neg hvw, hdP v hvP]
      · rw [if_neg hvP, if_neg hvw, hdR v hvw hvP]
  have hE : 2 * F.edgeFinset.card =
      Fintype.card (AType (colP k)) * (Fintype.card (CType (colP k)) - 1) := by
    have hsum : ∑ v, (F.degree v + (2 * (if v ∈ P then 1 else 0) +
        (if v = w then 12 * k ^ 2 + 8 * k + 2 else 0))) =
        ∑ _v : CType (colP k), (12 * k ^ 2 + 14 * k + 4) := sum_congr rfl fun v _ => hpt v
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_boole, sum_ite_eq', if_pos (mem_univ w),
      sum_const, card_univ, hcC, smul_eq_mul, F.sum_degrees_eq_twice_card_edges] at hsum
    have hPf : (univ.filter fun v => v ∈ P).card = P.card := by
      congr 1; ext v; simp
    rw [hPf] at hsum
    simp only [Nat.cast_id] at hsum
    rw [hcA, hcC, show 12 * k ^ 2 + 20 * k + 9 - 1 = 12 * k ^ 2 + 20 * k + 8 by omega]
    nlinarith [hsum, hPs]
  have heven : ∀ v, Even (Fintype.card (AType (colP k)) - F.degree v) := by
    intro v
    rw [hcA]
    by_cases hvw : v = w
    · subst hvw; rw [hdw]; exact ⟨6 * k ^ 2 + 4 * k + 1, by omega⟩
    · by_cases hvP : v ∈ P
      · rw [hdP v hvP]; exact ⟨1, by omega⟩
      · rw [hdR v hvw hvP]; exact ⟨0, by omega⟩
  -- L184
  obtain ⟨S, hSbic⟩ := l184_assembly (colP k) μ hμ hμ' F colour hproper hodd hE heven (prefixP d)
    hP3 hPbic hPres hPcov
  refine ⟨S, colP k, hSbic, ?_, ?_, ?_⟩
  · rw [classSize, ← Fintype.card_subtype]; exact card_classA
  · rw [classSize, ← Fintype.card_subtype]; exact card_classB
  · rw [classSize, ← Fintype.card_subtype]; exact card_classC

end CDRBicolour.Prefix
