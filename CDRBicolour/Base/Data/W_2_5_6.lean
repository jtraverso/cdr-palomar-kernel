/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Base.KernelTable

/-! The profile (2, 5, 6); the archived table re-encoded as natural numbers.
All table laws are checked by Lean's kernel, without native evaluation. -/

@[expose] public section
namespace CDRBicolour.Base.Data

def k_2_5_6 : Array (Array Nat) := #[
  #[0,6,3,2,5,4,1,10,9,8,7,12,11],
  #[6,1,4,5,2,3,0,12,10,11,8,9,7],
  #[3,4,2,0,1,8,7,6,5,12,11,10,9],
  #[2,5,0,3,12,1,11,8,7,10,9,6,4],
  #[5,2,1,12,4,0,10,9,11,7,6,8,3],
  #[4,3,8,1,0,5,9,11,2,6,12,7,10],
  #[1,0,7,11,10,9,6,2,12,5,4,3,8],
  #[10,12,6,8,9,11,2,7,3,4,0,5,1],
  #[9,10,5,7,11,2,12,3,8,0,1,4,6],
  #[8,11,12,10,7,6,5,4,0,9,3,1,2],
  #[7,8,11,9,6,12,4,0,1,3,10,2,5],
  #[12,9,10,6,8,7,3,5,4,1,2,11,0],
  #[11,7,9,4,3,10,8,1,6,2,5,0,12]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem realises_2_5_6 : Realises 2 5 6 :=
  realises_of_table 2 5 6 (natTable k_2_5_6 (2 + 5 + 6) (by norm_num))
    (by decide +kernel)

end CDRBicolour.Base.Data
