/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V40.MacroBank
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.ProtectedBank
open S07V40
variable {V Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]

/-- Keep the original host, charges and subgroups. Protection is enforced by
the on/off predicate, not by deleting a graph and changing its lattice. -/
def protect (S : MacroSetting V Q C) (F0 : Finset (Sym2 V)) : MacroSetting V Q C :=
  { S with basal := fun X => S.basal X ∧ Disjoint X F0 }

theorem protect_basal {S : MacroSetting V Q C} (F0 : Finset (Sym2 V))
    (hB : BasalInherit S) : BasalInherit (protect S F0) := by
  refine ⟨⟨hB.1,by simp⟩,?_⟩
  intro X Y hXY hX hY
  exact ⟨hB.2 X Y hXY hX.1 hY.1,disjoint_union_left.mpr ⟨hX.2,hY.2⟩⟩

theorem goodCell_protect {S : MacroSetting V Q C} (F0 B : Finset (Sym2 V))
    (Z : Finset V) (l : Lab C S.P) (c : Cell V)
    (hc : GoodCell S (B∪F0) Z l c) : GoodCell (protect S F0) B Z l c := by
  obtain ⟨hAY,hA,hTot,hDis,hAv,hSize,hCharge⟩ := hc
  have hF : Disjoint c.tot F0 := hDis.mono_right subset_union_right
  exact ⟨hAY,⟨hA,hF.mono_left subset_union_left⟩,⟨hTot,hF⟩,
    hDis.mono_right subset_union_left,hAv,hSize,hCharge⟩

/-- Every actually placed cell, hence the whole bank and all mode choices,
avoid the protected external edges. -/
theorem protected_bank_disjoint {S : MacroSetting V Q C} (F0 : Finset (Sym2 V))
    {L N : ℕ} (hM : MacroBank (protect S F0) L N) : Disjoint (Br (protect S F0) N) F0 := by
  have hCells : ∀ p ∈ run (protect S F0) N, Disjoint p.cell.tot F0 := by
    intro p hp
    exact (hM.cells p hp).1.2.2.1.2
  have hList : ∀ ps : List (Placed V C S.P),
      (∀ p ∈ ps, Disjoint p.cell.tot F0) → Disjoint (edgesOf ps) F0 := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih =>
      intro h
      exact disjoint_union_left.mpr ⟨h p (by simp),ih (fun p hp => h p (by simp [hp]))⟩
  exact hList _ hCells

end TypedTriangle.ProtectedBank
