/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.MainPaperIII
public import CDRBicolour.Absorption.Lattice
public import CDRBicolour.Absorption.Hinge

/-!
# Asymptotic CDR via Paper III (Theorem T)

Theorem T of Paper III (`TypedTriangle.Vortex.main_theorem_T`) turns the four hypotheses
H1 (diffuse seed), H2 (physical lattice), H3 (common neighbours) and H4 (hinges) into an
allowed triangle decomposition of all edges.  For the CDR host (complete graph labelled by
the three classes, bicoloured types) the four hypotheses are proved in this directory for
`n ≥ 400`:

* H1: `cdr_H1` (C = 4);
* H2: `cdr_H2` (direct lattice argument);
* H3: `cdr_H3'` (α = 1/32);
* H4: `cdr_H4` (α = 1/32, h = 6).

An allowed decomposition is a strictly bicoloured STS (`realises_of_decomposition`).
Hence every admissible profile of sufficiently large order is realised.  The threshold
`n₀` comes from Theorem T and is not explicit.  No external hypothesis is used.
-/

@[expose] public section

namespace CDRBicolour.Absorption

open TypedTriangle

/-- **Asymptotic CDR, without external hypotheses.** Every admissible profile `(a, b, c)` of
sufficiently large order `a + b + c` is realised by a 3-bicoloured STS. -/
theorem cdr_eventually :
    ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c → Realises a b c := by
  obtain ⟨n₀, hT⟩ := Vortex.main_theorem_T cdrF (1 / 32) 4 6 (by norm_num) (by norm_num) le_rfl
  refine ⟨max n₀ 400, fun a b c h hn => ?_⟩
  have h400 : 400 ≤ a + b + c := le_of_max_le_right hn
  obtain ⟨D, hD⟩ := hT (cdrHost a b c) (by rw [Fintype.card_fin]; exact le_of_max_le_left hn)
    ⟨_, cdr_H1 h h400⟩ (cdr_H2 h h400) (cdr_H3' h h400) (cdr_H4 h h400)
  exact realises_of_decomposition D hD

end CDRBicolour.Absorption
