/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V47.Uniform
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
open S07V40 S07V42 S07V43 S07V44 S07V46 S07V47

/-- The ACTUAL bank is the union of all its strata, including the strata
left unused by an early-stopping allocation. -/
theorem all_strata_total {V Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]
    {S : MacroSetting V Q C} {L N : ℕ} (hM : MacroBank S L N) :
    (range (L+1)).biUnion (fun i => (stratBank S N i).total) = Br S N := by
  apply Subset.antisymm
  · exact biUnion_subset.mpr (fun _ _ => stratBank_total_subset)
  · intro e he
    obtain ⟨p,hp,hep⟩ := mem_edgesOf.mp he
    obtain ⟨k,hk⟩ := List.get_of_mem hp
    let j := sidx S p.round
    have hj : j ≤ L := hM.strata_le p.round (hM.cells p hp).2.1
    have hk' : sidx S ((run S N).get k).round = j := by rw [hk]
    refine mem_biUnion.mpr ⟨j,mem_range.mpr (by omega),?_⟩
    apply mem_biUnion.mpr
    refine ⟨⟨k,hk'⟩,mem_univ _,?_⟩
    change e ∈ ((run S N).get k).cell.tot
    rwa [hk]

/-- Pay the WHOLE bank after activating only strata through J. Unused
strata retain their total basal mode; they are not silently discarded.
This also covers J=0 and a bank that executed no rounds. -/
theorem whole_bank_cover {V Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]
    {S : MacroSetting V Q C} {L N J : ℕ} (hM : MacroBank S L N)
    (hB : Inherit S.basal) (hJ : J ≤ L)
    (z : ℕ → Fin S.P → C → ℤ) (hs : ∀ i, (stratBank S N i).Supplies (z i))
    (htd : ∀ i j, i ≠ j → Disjoint (stratBank S N i).total (stratBank S N j).total) :
    ∃ Bc : Finset (Sym2 V), S.basal Bc ∧
      Br S N = Bc ∪ (range (J+1)).biUnion (fun i => Bank.payload (hs i)) ∧
      Disjoint Bc ((range (J+1)).biUnion (fun i => Bank.payload (hs i))) := by
  let mode : ℕ → Finset (Sym2 V) := fun i =>
    if i ≤ J then Bank.cover (hs i) else (stratBank S N i).total
  have hSub : ∀ i, mode i ⊆ (stratBank S N i).total := by
    intro i
    dsimp only [mode]
    split_ifs
    · exact Bank.cover_subset_total _
    · exact subset_rfl
  have hBas : ∀ i, S.basal (mode i) := by
    intro i
    dsimp only [mode]
    split_ifs
    · exact Bank.basal_cover (hs i) hB (stratBank_valid hM)
    · exact Bank.basal_total hB (stratBank_valid hM)
  let Bc := (range (L+1)).biUnion mode
  refine ⟨Bc,inherit_biUnion hB hBas
    (fun i j hij => ((htd i j hij).mono_left (hSub i)).mono_right (hSub j)) _,?_,?_⟩
  · rw [←all_strata_total hM]
    apply Subset.antisymm
    · intro e he
      obtain ⟨i,hi,he⟩ := mem_biUnion.mp he
      by_cases hiJ : i ≤ J
      · rw [←Bank.cover_union_payload (hs i) (stratBank_valid hM)] at he
        rcases mem_union.mp he with he | he
        · exact mem_union_left _ (mem_biUnion.mpr ⟨i,hi,by simpa [mode,hiJ] using he⟩)
        · exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_range.mpr (by omega),he⟩)
      · exact mem_union_left _ (mem_biUnion.mpr ⟨i,hi,by simpa [mode,hiJ] using he⟩)
    · intro e he
      rcases mem_union.mp he with he | he
      · obtain ⟨i,hi,he⟩ := mem_biUnion.mp he
        exact mem_biUnion.mpr ⟨i,hi,hSub i he⟩
      · obtain ⟨i,hi,he⟩ := mem_biUnion.mp he
        exact mem_biUnion.mpr ⟨i,mem_range.mpr (by simp only [mem_range] at hi; omega),
          Bank.payload_subset_total (hs i) he⟩
  · apply disjoint_left.mpr
    intro e hec hey
    obtain ⟨i,hi,hec⟩ := mem_biUnion.mp hec
    obtain ⟨j,hj,hey⟩ := mem_biUnion.mp hey
    by_cases hij : i = j
    · subst j
      have hiJ : i ≤ J := by simpa only [mem_range] using (Nat.lt_succ_iff.mp (mem_range.mp hj))
      have hic : e ∈ Bank.cover (hs i) := by simpa [mode,hiJ] using hec
      exact disjoint_left.mp (Bank.disjoint_cover_payload (hs i) (stratBank_valid hM)) hic hey
    · exact disjoint_left.mp (htd i j hij) (hSub i hec) (Bank.payload_subset_total (hs j) hey)

/-- From the ACTUAL protected allocation, obtain an intrinsically physical
indicator on the same core, together with the basal complement of the entire
bank. Integer class cancellation is converted to a set union only AFTER
proving disjointness from the actual leftover. -/
theorem activated_child_and_whole_complement {V I : Type*} [Fintype V]
    {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V}
    {d c E Rc P q Ecell zmax L N J : ℕ}
    (C0 : CoreCompression H lab F W d c E) (F0 : Finset (Sym2 V))
    (hM : MacroBank (protSetting C0 Rc P q Ecell zmax F0) L N) (hJ : J ≤ L)
    (Y : Finset (Sym2 V)) (hYF : Y ⊆ F0)
    (x : MCore H lab F W) (hx : (x : Sym2 V → ℤ) = SparseEdge.ind Y)
    (hout : ProtOutcome C0 Rc P q Ecell zmax F0 N J x) :
    ∃ Yb Bc : Finset (Sym2 V),
      physBasal H lab F Bc ∧ Disjoint Bc F0 ∧
      Br (protSetting C0 Rc P q Ecell zmax F0) N = Bc∪Yb ∧
      Disjoint Bc Yb ∧ Disjoint Y Yb ∧
      SparseEdge.ind (Y∪Yb) ∈ LamCore H lab F W ∧
      Yb ⊆ childEdges H W := by
  let S := protSetting C0 Rc P q Ecell zmax F0
  obtain ⟨z,hs,hprops,hAllDis,hYDis,hCDis⟩ := hout
  obtain ⟨hact,hcap,hPA,hAvoid,htd,hcharge,hphys,hPart,hDis,hBasTot,hBasCov,hPhysCov,hcard⟩ := hprops
  have hShape := protSetting_shape C0 Rc P q Ecell zmax F0
  obtain ⟨Bc,hBc,hWhole,hBcDis⟩ := whole_bank_cover hM hShape.basal_inherit hJ z hs htd
  let Yb := (range (J+1)).biUnion (fun i => Bank.payload (hs i))
  have hYbSub : Yb ⊆ childEdges H W := by
    intro e he
    obtain ⟨i,hi,he⟩ := mem_biUnion.mp he
    obtain ⟨k,hk,hek⟩ := mem_biUnion.mp he
    exact (shape_stratBank_valid hShape hM i).2 k hek
  have hYYb : Disjoint Y Yb := (hYDis.mono_right hYF).symm
  have hFinal : SparseEdge.ind (Y∪Yb) ∈ LamCore H lab F W := by
    rw [S07V43.ind_union_of_disjoint hYYb]
    rw [←hx]
    exact hphys
  exact ⟨Yb,Bc,hBc.1,hBc.2,hWhole,hBcDis,hYYb,hFinal,hYbSub⟩

end TypedTriangle.CatalogNative
