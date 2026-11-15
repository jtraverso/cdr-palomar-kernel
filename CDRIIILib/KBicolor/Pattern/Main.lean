/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Pattern.ExistsMain
public import CDRIIILib.Palomar.GaleHoffman

/-!
# k-bicoloured Latin patterns (unconditional)

`exists_kbls`: for `k ≥ 4` and every admissible k-profile `c` of order `n` with classes `≥ δ n` and
an η-seed, if `n` is large there is a k-bicoloured Latin square of **bounded** order `N ≤ B`
(points `Σ P, Fin (m P)`, class of a point = its first coordinate) whose class proportions are
within `ε` of `c / n`. Gale's theorem is discharged from Palomar 000015 (`Palomar.galeInt`).

This is the pattern that replaces the 3 × 3 class pattern `τ` of the k = 3 Wilson construction
(`Count.Wilson.Cross`), which has no analogue with one part per class when `k ≥ 4`.
-/

@[expose] public section

namespace CDRBicolour.KBicolor.Pattern

open Finset

variable {k : ℕ}

theorem csize_sigma (m : Fin k → ℕ) (P : Fin k) :
    Hilton.csize (fun x : (Σ Q, Fin (m Q)) => x.1) P = m P := by
  unfold Hilton.csize
  rw [Fintype.card_congr (Equiv.sigmaSubtype P), Fintype.card_fin]

theorem exists_kbls (hk : 4 ≤ k) {δ η ε : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ B : ℕ, ∃ n₀ : ℕ, ∀ (n : ℕ) (c : Fin k → ℕ), n₀ ≤ n → ∑ P, c P = n →
      3 * ∑ P, (c P : ℝ) ^ 2 = (n : ℝ) ^ 2 + 2 * n → (∀ P, δ * n ≤ c P) →
      (∃ a, SeedData c η a) →
      ∃ m : Fin k → ℕ, (∀ P, 1 ≤ m P) ∧ ∑ P, m P ≤ B ∧
        (∀ P, |(m P : ℝ) / (∑ Q, m Q : ℕ) - c P / n| ≤ ε) ∧
        ∃ L : (Σ P, Fin (m P)) → (Σ P, Fin (m P)) → (Σ P, Fin (m P)),
          (∀ a, Function.Bijective (L a)) ∧ (∀ b, Function.Bijective (fun a => L a b)) ∧
          ∀ a b, bic a.1 b.1 (L a b).1 := by
  obtain ⟨B, n₀, h⟩ := exists_pattern Palomar.galeInt hk hδ hη hε
  refine ⟨B, n₀, fun n c hn hsum hsq hcls hseed => ?_⟩
  obtain ⟨m, hm1, hB, -, hclose, x, hx⟩ := h n c hn hsum hsq hcls hseed
  exact ⟨m, hm1, hB, hclose,
    kbls_of_tournament (fun a : (Σ P, Fin (m P)) => a.1) (csize_sigma m) hx⟩

end CDRBicolour.KBicolor.Pattern
