/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.PaperIII.ArithMain
public import CDRBicolour.PaperIII.Near
public import CDRBicolour.PaperIII.GalePalomar

/-!
# CDR Paper III — Theorem K (T6): every `k ≥ 4` is eventually realised

For every `k ≥ 4` there is `v₀` such that every admissible `v ≥ v₀` carries a `k`-bicolourable
Steiner triple system. External inputs, as hypotheses:
* `GaleInt` — Gale's Feasibility Theorem, integer version (Palomar PALOMAR-2026-11-06-000015);
* `ThreeSquaresDense` — Duke–Schulze-Pillot (1990).

* `k = 4`: `conj35_large` (CDR Conjecture 3.5 for large `v`).
* `k ≥ 5`: the geometric profile (`geometric_profile`, T4) satisfies the criterion, so
  `near_profile_bicolourable` (T5) applies to every split within `ρ v` of it, and `split_near`
  provides such a split for every large admissible `v`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.PaperIII

open Finset

/-- **Theorem K (T6).** -/
theorem bicolourable_eventually (hG : GaleInt) (hA : ThreeSquaresDense) {k : ℕ} (hk : 4 ≤ k) :
    ∃ v₀ : ℕ, ∀ v, v₀ ≤ v → Admissible v → Bicolourable v k := by
  rcases Nat.eq_or_lt_of_le hk with rfl | hk5
  · exact conj35_large hA
  have hk5' : 5 ≤ k := hk5
  obtain ⟨p, hp, h1, h2, hsym, hne, hcrit⟩ := geometric_profile k hk5'
  obtain ⟨ρ, hρ, v₁, hnear⟩ := near_profile_bicolourable hG (by omega) p hp h1 h2 hcrit
  obtain ⟨V₀, hsplit⟩ := split_near hA hk5' p hp h1 h2 hsym hne hρ
  refine ⟨max v₁ V₀, fun v hv hadm => ?_⟩
  obtain ⟨c, hsum, hdiv, hpar, hclose⟩ := hsplit v (le_of_max_le_right hv) hadm
  have hodd : Odd v := Nat.odd_iff.2 (by rcases hadm with h | h <;> omega)
  exact hnear v (le_of_max_le_left hv) hodd c hsum hdiv hpar hclose

/-- **CDR Conjecture 3.6 for large `v`** (the case `k = 5` of Theorem K). -/
theorem conj36_large (hG : GaleInt) (hA : ThreeSquaresDense) :
    ∃ v₀ : ℕ, ∀ v, v₀ ≤ v → Admissible v → Bicolourable v 5 :=
  bicolourable_eventually hG hA (by norm_num)

/-- **Theorem K**, with Gale's input in the exact form registered in Palomar
(PALOMAR-2026-11-06-000015 v1, `GaleHoffman.feasibility_int`). -/
theorem bicolourable_eventually_palomar (hG : PalomarFeasibilityInt) (hA : ThreeSquaresDense)
    {k : ℕ} (hk : 4 ≤ k) : ∃ v₀ : ℕ, ∀ v, v₀ ≤ v → Admissible v → Bicolourable v k :=
  bicolourable_eventually (galeInt_of_palomar hG) hA hk

end CDRBicolour.PaperIII
