/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.BRIFinal

/-!
# H1 for residual CDR hosts (backlog item 2a), unconditional

For an admissible profile with `n ≥ 2040` and a packing `P` of bicoloured triangles whose leave
has maximum degree `Δ` with `6656000 Δ ≤ n`, the residual host `K_n − E(P)` has a diffuse seed
with constant `8` (`cdr_residual_seed`): the type-uniform seed of the complete host (`cdr_H1`,
`C₀ = 4`) is corrected by the bounded right inverse (`bri_of_balanced`, `K = 52000`) through
`residual_seed_of_bri` (`8 · 52000 · 4² = 6656000`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

/-- **Residual H1 for the CDR host.** -/
theorem cdr_residual_seed {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 2040 ≤ a + b + c)
    (P : Finset (Finset (Fin (a + b + c)))) (hP : ∀ T ∈ P, IsAllowed (cdrHost a b c) cdrF T)
    (hPd : (P : Set (Finset (Fin (a + b + c)))).PairwiseDisjoint triEdges) {Δ : ℕ}
    (hdeg : ∀ p, degL (P.biUnion triEdges) p ≤ Δ) (hΔ : 6656000 * Δ ≤ a + b + c) :
    ∃ μ, IsDiffuseSeed (rHost (col3 a b c) (P.biUnion triEdges)) cdrF 8 μ := by
  have h400 : 400 ≤ a + b + c := by omega
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h h400
  have hs0 := csz_col3 a b c 0
  have hs1 := csz_col3 a b c 1
  have hs2 := csz_col3 a b c 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hs0 hs1 hs2
  set m := (a + b + c + 8) / 4 with hm_def
  have hm : ∀ k, m ≤ csz (col3 a b c) k := by
    intro k; fin_cases k <;> simp [csz_col3] <;> omega
  have h512 : 512 ≤ m := by omega
  have hbal : Fintype.card (Fin (a + b + c)) ≤ 4 * m := by rw [Fintype.card_fin]; omega
  obtain ⟨B⟩ := bri_of_balanced hm h512 hbal
  have := residual_seed_of_bri (K := 52000) (C₀ := 4) (by norm_num) (by norm_num) B
    (cdr_H1 h h400) P (fun T hT => mem_tri.mpr (hP T hT)) hPd hdeg
    (by rw [Fintype.card_fin]; omega)
    (by rw [Fintype.card_fin]; push_cast; have : (6656000 * Δ : ℝ) ≤ a + b + c := by
          exact_mod_cast hΔ
        nlinarith)
  norm_num at this
  exact this

end CDRBicolour.Absorption
