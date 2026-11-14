/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.PaperIII.Main
public import GaleHoffmanSolution

/-!
# Gale's feasibility theorem from Palomar: Theorem K with Duke–Schulze-Pillot as only input

`GaleHoffman.feasibility_int` (`jtraverso/gale-hoffman-feasibility` @ `fa52c29`, Palomar
**PALOMAR-2026-11-06-000015 v1**) discharges `PalomarFeasibilityInt`, hence `GaleInt`.
The only remaining external input of CDR Paper III is `ThreeSquaresDense`
(Duke–Schulze-Pillot 1990).
-/

@[expose] public section

namespace CDRBicolour.Palomar

open CDRBicolour.PaperIII

theorem palomarFeasibilityInt : PalomarFeasibilityInt :=
  fun _ _ _ c hc d => GaleHoffman.feasibility_int c hc d

theorem galeInt : GaleInt := galeInt_of_palomar palomarFeasibilityInt

/-- **Theorem K** (CDR Paper III): for every `k ≥ 4`, every large admissible order carries a
`k`-bicolourable STS. Only external input: Duke–Schulze-Pillot. -/
theorem bicolourable_eventually_dsp (hA : ThreeSquaresDense) {k : ℕ} (hk : 4 ≤ k) :
    ∃ v₀ : ℕ, ∀ v, v₀ ≤ v → Admissible v → Bicolourable v k :=
  bicolourable_eventually galeInt hA hk

/-- **CDR Conjecture 3.6 for large orders**, Duke–Schulze-Pillot as only input. -/
theorem conj36_large_dsp (hA : ThreeSquaresDense) :
    ∃ v₀ : ℕ, ∀ v, v₀ ≤ v → Admissible v → Bicolourable v 5 :=
  conj36_large galeInt hA

end CDRBicolour.Palomar
