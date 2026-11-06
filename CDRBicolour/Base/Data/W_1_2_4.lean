/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Base.KernelTable

/-! The profile (1, 2, 4); the archived table re-encoded as natural numbers.
All table laws are checked by Lean's kernel, without native evaluation. -/

@[expose] public section
namespace CDRBicolour.Base.Data

def k_1_2_4 : Array (Array Nat) := #[
  #[0,2,1,4,3,6,5],
  #[2,1,0,6,5,4,3],
  #[1,0,2,5,6,3,4],
  #[4,6,5,3,0,2,1],
  #[3,5,6,0,4,1,2],
  #[6,4,3,2,1,5,0],
  #[5,3,4,1,2,0,6]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem realises_1_2_4 : Realises 1 2 4 :=
  realises_of_table 1 2 4 (natTable k_1_2_4 (1 + 2 + 4) (by norm_num))
    (by decide +kernel)

end CDRBicolour.Base.Data
