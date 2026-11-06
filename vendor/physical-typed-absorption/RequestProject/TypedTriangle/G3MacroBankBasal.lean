/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V47.Shape
public import RequestProject.S07V40.MacroBank
public import RequestProject.TypedTriangle.SlotPairing
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section

namespace S07V40

/-- Choosing the on mode in every placed cell gives the entire bank. -/
theorem all_on_mode_eq_bank {V Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]
    {S : MacroSetting V Q C} (N : ℕ) :
    modeUnion (fun _ => true) (run S N) = Br S N := by
  unfold Br
  induction run S N with
  | nil => rfl
  | cons p rest ih =>
      simp only [modeUnion, modeSet, edgesOf, ih]
      simp

/-- The total bank, not merely each selected mode, is basal. -/
theorem MacroBank.total_basal {V Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]
    {S : MacroSetting V Q C} {L N : ℕ} (hM : MacroBank S L N) :
    S.basal (Br S N) := by
  rw [← all_on_mode_eq_bank N]
  exact hM.modes_basal (fun _ => true)

end S07V40

namespace S07V47

open S07V42 S07V43 S07V40

/-- For the protected physical setting, the whole bank has an original-host
triangle decomposition and avoids its protected edge set. -/
theorem protected_total_bank_basal {V I : Type*} [Fintype V]
    {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {W : Finset V} {d c E R P q Ecell zmax L N : ℕ}
    (C0 : CoreCompression H lab F W d c E) (F0 : Finset (Sym2 V))
    (hM : S07V40.MacroBank (protSetting C0 R P q Ecell zmax F0) L N) :
    physBasal H lab F (S07V40.Br (protSetting C0 R P q Ecell zmax F0) N) ∧
      Disjoint (S07V40.Br (protSetting C0 R P q Ecell zmax F0) N) F0 :=
  hM.total_basal

end S07V47
