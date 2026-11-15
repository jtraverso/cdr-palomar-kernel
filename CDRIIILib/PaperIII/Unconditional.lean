/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.PaperIII.UnconditionalArithmetic
public import CDRIIILib.PaperIII.SeedMargin70

/-! # CDR Paper III: unconditional eventual existence and sharp four-colour counts

The original conditional interfaces are preserved. The arithmetic input is now
supplied by its proof, and Gale's integer feasibility theorem is already proved.
The thresholds remain existential because the cap proof uses Siegel's theorem.
-/

@[expose] public section
noncomputable section

namespace CDRBicolour.PaperIII
open CDRBicolour.KBicolor

theorem meridianThreeSquaresDense_verified : MeridianThreeSquaresDense :=
  meridian_of_threeSquaresDense threeSquaresDense_verified

/-- Theorem K, with both external contracts discharged by proofs. -/
theorem bicolourable_eventually_unconditional {k : ℕ} (hk : 4 ≤ k) :
    ∃ v₀ : ℕ, ∀ v, v₀ ≤ v → Admissible v → Bicolourable v k :=
  bicolourable_eventually_with_registered_gale threeSquaresDense_verified hk

/-- CDR Conjecture 3.5 for every sufficiently large admissible order. -/
theorem conj35_large_unconditional :
    ∃ v₀ : ℕ, ∀ v, v₀ ≤ v → Admissible v → Bicolourable v 4 :=
  bicolourable_eventually_unconditional (by norm_num)

/-- CDR Conjecture 3.6 for every sufficiently large admissible order. -/
theorem conj36_large_unconditional :
    ∃ v₀ : ℕ, ∀ v, v₀ ≤ v → Admissible v → Bicolourable v 5 :=
  bicolourable_eventually_unconditional (by norm_num)

theorem capRep_eventually_verified :
    ∃ V₀ : ℕ, ∀ v, V₀ ≤ v → Admissible v → CapRep v :=
  capRep_eventually threeSquaresDense_verified

theorem two_cap_at_verified : ∃ N₀ : ℕ, TwoCapAt N₀ :=
  threeSquaresDense_supplies_two_cap threeSquaresDense_verified

theorem cap_two_eventually_verified :
    ∃ V₀ : ℕ, ∀ v, V₀ ≤ v → Admissible v → CapRepTwo v :=
  cap_two_eventually_of_radius_caps two_cap_at_verified

/-- The same labelled profile satisfies both bounds; no arithmetic input remains. -/
theorem four_colour_sharp_counting_eventually {ε : ℝ} (hε : 0 < ε) :
    ∃ V₀ : ℕ, ∀ v, V₀ ≤ v → Admissible v →
      ∃ lab : Fin v → Fin 4, (∀ X, 0 < ksz lab X) ∧ 0 < kCount lab ∧
        (1/6-ε)*(v : ℝ)^2*Real.log v ≤ Real.log (kCount lab) ∧
        Real.log (kCount lab) ≤ (1/6+ε)*(v : ℝ)^2*Real.log v := by
  obtain ⟨N₀, hN⟩ := two_cap_at_verified
  exact ⟨max N₀ (capTwoCountingThreshold70 ε),
    fun v hv hadm => sharp_counting_at_two_cap_threshold70 hN hε hv hadm⟩

end CDRBicolour.PaperIII
