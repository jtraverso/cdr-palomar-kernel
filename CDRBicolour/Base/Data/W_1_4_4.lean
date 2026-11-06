/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Base.KernelTable

/-! The profile (1, 4, 4); the archived table re-encoded as natural numbers.
All table laws are checked by Lean's kernel, without native evaluation. -/

@[expose] public section
namespace CDRBicolour.Base.Data

def k_1_4_4 : Array (Array Nat) := #[
  #[0,2,1,4,3,7,8,5,6],
  #[2,1,0,8,7,6,5,4,3],
  #[1,0,2,5,6,3,4,8,7],
  #[4,8,5,3,0,2,7,6,1],
  #[3,7,6,0,4,8,2,1,5],
  #[7,6,3,2,8,5,1,0,4],
  #[8,5,4,7,2,1,6,3,0],
  #[5,4,8,6,1,0,3,7,2],
  #[6,3,7,1,5,4,0,2,8]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem realises_1_4_4 : Realises 1 4 4 :=
  realises_of_table 1 4 4 (natTable k_1_4_4 (1 + 4 + 4) (by norm_num))
    (by decide +kernel)

end CDRBicolour.Base.Data
