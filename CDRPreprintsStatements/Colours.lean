/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in LICENSE.
-/
module

public import CDRPreprintsStatements.Basic
public import Mathlib

@[expose] public section
namespace CDRBicolour

namespace Prefix
def col3 (a b c : ℕ) (v : Fin (a + b + c)) : Fin 3 :=
  if v.val < a then 0 else if v.val < a + b then 1 else 2
end Prefix

namespace BlockTypes
def cnt {V : Type*}
    (col : V → Fin 3) (j : Fin 3) (B : Finset V) : ℕ :=
  (B.filter fun y => col y = j).card

def typeCount {V : Type*} [DecidableEq V]
    (S : STS V) (col : V → Fin 3) (i j : Fin 3) : ℕ :=
  (S.blocks.filter fun B => cnt col i B = 2 ∧ cnt col j B = 1).card
end BlockTypes


end CDRBicolour
