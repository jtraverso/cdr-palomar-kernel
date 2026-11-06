/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Route
public import CDRBicolour.Palomar.DinitzStinson
public import CDRBicolour.Palomar.RudasovaSotak
public import CDRBicolour.Palomar.BKLS

/-!
# The Colbourn–Dinitz–Rosa characterization

`cdr_characterization`: a profile `(a, b, c)` with three nonempty classes is realised by a strictly
bicoloured STS **if and only if** it is admissible.  **Unconditional.**

* necessity: `Palomar.admissible_of_realises` (Dinitz–Stinson Proposition 1.2, Palomar
  PALOMAR-2026-11-04-000014);
* sufficiency: `cdr_conjecture`, from `cdr_conjecture_of_branches` with
  Balister–Kostochka–Li–Schelp Corollary 12 (`Palomar.bkls_corollary_12`,
  `jtraverso/balanced-edge-colourings` @ `736c78e`) and Rudašová–Soták Theorem 3.1
  (`Palomar.rs_theorem_3_1`, PALOMAR-2026-11-05-000001).
-/

@[expose] public section

namespace CDRBicolour

/-- **The Colbourn–Dinitz–Rosa conjecture**, conditional only on BKLS Corollary 12. -/
theorem cdr_conjecture_of_BKLS (hBK : Master.BKLS_Corollary_12.{0}) : CDRConjecture :=
  cdr_conjecture_of_branches hBK Palomar.rs_theorem_3_1

/-- **The Colbourn–Dinitz–Rosa conjecture.** -/
theorem cdr_conjecture : CDRConjecture :=
  cdr_conjecture_of_BKLS Palomar.bkls_corollary_12

/-- **CDR characterization**: realised ⇔ admissible (three nonempty classes). -/
theorem cdr_characterization {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Realises a b c ↔ AdmissibleProfile a b c :=
  ⟨Palomar.admissible_of_realises ha hb hc, cdr_conjecture a b c⟩

/-- The same, in the language of the Palomar entry (`CDR.Bicolourable3`). -/
theorem cdr_characterization_bicolourable3 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    CDR.Bicolourable3 (a + b + c) a b c ↔ AdmissibleProfile a b c :=
  (Palomar.realises_iff_bicolourable3 a b c).symm.trans (cdr_characterization ha hb hc)

end CDRBicolour
