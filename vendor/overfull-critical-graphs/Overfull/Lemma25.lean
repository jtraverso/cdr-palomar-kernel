/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Degree

/-!
# CCJS Lemma 2.5 (degree dichotomy)

Let `G` be `Δ`-critical, `ab ∈ E(G)` with `d(b) = Δ`, `k = d(a)`, and `φ` a colouring of `G − ab`
with `Δ` colours. Then:

* `no_two_inA`: if `v ∉ {a, b}` and `n + 2k + [av ∈ E] ≤ d(v) + Δ + 5`, at most one colour of
  `A = φ̄(a) ∪ φ̄(b)` is missing at `v`;
* `degree_dichotomy`: no `v ≠ a` has `n − Δ + 2k − 5 ≤ d(v) ≤ Δ − k`.

The proof finds `w` adjacent to `b` and `v` with both edges coloured in `A`, so that `a b w v` is a
Kierstead path, and applies CCJS Lemma 2.4 (b).
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : PEC G (Fin G.maxDegree)} {a b : V}

/-- `|nonA| = d(a) − 2` when `d(b) = Δ`. -/
theorem IsColMinus.card_nonA_eq (hG : IsClassTwo G) (hcm : IsColMinus c a b)
    (hdb : G.degree b = G.maxDegree) : #(nonA c a b) + 2 = G.degree a := by
  have h1 := hcm.card_nonA hG
  have h2 := hcm.card_missing_end (Or.inl rfl)
  have h3 := hcm.card_missing_end (Or.inr rfl)
  omega

/-- At most one colour of `A` is missing at `v`. -/
theorem no_two_inA (hG : IsDeltaCritical G) (hcm : IsColMinus c a b)
    (hdb : G.degree b = G.maxDegree) {v : V} (hva : v ≠ a) (hvb : v ≠ b)
    (hcnt : Fintype.card V + 2 * G.degree a + (if G.Adj v a then 1 else 0) ≤
      G.degree v + G.maxDegree + 5)
    {θ₁ θ₂ : Fin G.maxDegree} (hne : θ₁ ≠ θ₂) (h₁ : InA c a b θ₁) (h₂ : InA c a b θ₂)
    (hv₁ : c.IsFree v θ₁) (hv₂ : c.IsFree v θ₂) : False := by
  obtain ⟨hdis, -⟩ := hcm.ab_facts hG.2.1
  have hδa : ∀ {x δ}, c.col b x = some δ → InA c a b δ → c.IsFree a δ := fun hx hA =>
    hA.resolve_right fun hb => hb _ hx
  by_cases hbv : G.Adj b v ∧ Good c a b b v
  · obtain ⟨-, δ, hδ, hδA⟩ := hbv
    obtain ⟨hA, hB⟩ := fan_bau hG.2.1 hcm hδ (hδa hδ hδA) hva.symm
    rcases h₁ with h | h
    · exact hA θ₁ h hv₁
    · exact hB θ₁ h hv₁
  have hk := hcm.card_nonA_eq hG.2.1 hdb
  obtain ⟨w, hwa, hwb, hwv, hbw, hvw, ⟨δ, hδ, hδA⟩, ⟨γ, hγ, hγA⟩⟩ :=
    exists_good_common₂ hG.2.1 hcm hva hvb (fun h hg => hbv ⟨h, hg⟩) (by rw [hdb]; omega)
  have hK : IsK4 c a b w v δ γ :=
    ⟨hcm, hδ, by rw [c.col_symm]; exact hγ, hδa hδ hδA, hγA, hwa.symm, hva.symm, hvb.symm⟩
  exact hK.not_two_common hG.2.1 hne h₁ h₂ hv₁ hv₂

/-- Two distinct colours of `A` are missing at `v` as soon as `d(v) ≤ Δ − d(a)`. -/
theorem exists_two_inA (hG : IsClassTwo G) (hcm : IsColMinus c a b)
    (hdb : G.degree b = G.maxDegree) {v : V} (hva : v ≠ a) (hvb : v ≠ b)
    (hdv : G.degree v + G.degree a ≤ G.maxDegree) :
    ∃ θ₁ θ₂, θ₁ ≠ θ₂ ∧ InA c a b θ₁ ∧ InA c a b θ₂ ∧ c.IsFree v θ₁ ∧ c.IsFree v θ₂ := by
  classical
  have hk := hcm.card_nonA_eq hG hdb
  have hm := hcm.card_missing_other hva hvb
  have hsub : missing c v ⊆ (missing c v).filter (InA c a b) ∪ nonA c a b := by
    intro θ hθ
    by_cases h : InA c a b θ
    · exact mem_union_left _ (mem_filter.2 ⟨hθ, h⟩)
    · exact mem_union_right _ (mem_nonA.2 h)
  have := (card_le_card hsub).trans (card_union_le _ _)
  obtain ⟨θ₁, h1, θ₂, h2, hne⟩ := one_lt_card.1 (show 1 < #((missing c v).filter (InA c a b))
    by omega)
  simp only [mem_filter, mem_missing] at h1 h2
  exact ⟨θ₁, θ₂, hne, h1.2, h2.2, h1.1, h2.1⟩

/-- **CCJS Lemma 2.5** (first part). No vertex `v ≠ a` has `n − Δ + 2d(a) − 5 ≤ d(v) ≤ Δ − d(a)`. -/
theorem degree_dichotomy (hG : IsDeltaCritical G) (hcm : IsColMinus c a b)
    (hdb : G.degree b = G.maxDegree) (ha2 : 2 ≤ G.degree a) {v : V} (hva : v ≠ a)
    (hlo : Fintype.card V + 2 * G.degree a ≤ G.degree v + G.maxDegree + 5)
    (hhi : G.degree v + G.degree a ≤ G.maxDegree) : False := by
  have hvb : v ≠ b := by
    rintro rfl
    omega
  have hnadj : ¬ G.Adj v a := by
    intro h
    have h1 := val_crit hG h.symm
    have h2 := card_maxNbrs_le h.symm
    omega
  obtain ⟨θ₁, θ₂, hne, h₁, h₂, hv₁, hv₂⟩ := exists_two_inA hG.2.1 hcm hdb hva hvb hhi
  exact no_two_inA hG hcm hdb hva hvb (by rw [if_neg hnadj]; omega) hne h₁ h₂ hv₁ hv₂

end Overfull
