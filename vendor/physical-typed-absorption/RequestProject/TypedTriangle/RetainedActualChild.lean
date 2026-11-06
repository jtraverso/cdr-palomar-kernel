/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.PositiveTransitionGlue
public import RequestProject.TypedTriangle.RawSeedDeletion
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.RawReference
variable {V I : Type*} [Fintype V]

/-- Keep the dense reference C protected while executing both the withdrawal
mode and the whole bank. The actual complement is C union the paid payload;
it is not the sparse payload alone. -/
theorem transition_retaining_reference (H : Host V I) (F : Set (Multiset I))
    (B C R : Finset (Sym2 V)) (Q : Finset (Finset V))
    (hB : B ⊆ edges H) (hC : C ⊆ edges H) (hR : R ⊆ edges H)
    (hBC : Disjoint B C) (hBCR : Disjoint (B∪C) R)
    (hQ : IsPacking H F Q) (hQdis : Disjoint (Q.biUnion triEdges) ((B∪C)∪R))
    (Ps Y Bc Yb : Finset (Sym2 V))
    (hMode : R∪(edges H\(((B∪C)∪R)∪Q.biUnion triEdges)) = Ps∪Y)
    (hPY : Disjoint Ps Y) (hPs : Basal H F Ps)
    (hBank : B = Bc∪Yb) (hBankDis : Disjoint Bc Yb) (hBc : Basal H F Bc) :
    ∃ Qf : Finset (Finset V), IsPacking H F Qf ∧
      Disjoint (Qf.biUnion triEdges) C ∧
      edges H\Qf.biUnion triEdges = C∪(Y∪Yb) := by
  obtain ⟨Q',hQ',hQ'BC,hRem⟩ := StockEntry.positive_stock_transition_glue H F
    (B∪C) R Q hR hBCR hQ hQdis Ps Y hMode hPY hPs
  have hBcB : Bc ⊆ B := by rw [hBank]; exact subset_union_left
  have hQ'Bc : Disjoint (Q'.biUnion triEdges) Bc :=
    hQ'BC.mono_right (hBcB.trans subset_union_left)
  obtain ⟨Db,hDb⟩ := hBc
  have hDec := hQ'.isDecomposition.union hDb hQ'Bc
  have hEf : (Q'∪Db).biUnion triEdges = Q'.biUnion triEdges∪Bc := hDec.2.2
  have hBcC : Disjoint Bc C := hBC.mono_left hBcB
  refine ⟨Q'∪Db,⟨hDec.1,hDec.2.1⟩,?_,?_⟩
  · rw [hEf,disjoint_union_left]
    exact ⟨hQ'BC.mono_right subset_union_right,hBcC⟩
  · rw [hEf]
    ext e
    have hr := (Finset.ext_iff.mp hRem) e
    have hb := (Finset.ext_iff.mp hBank) e
    have hcb : e ∈ C → e ∉ B := fun hc hb => disjoint_left.mp hBC hb hc
    have hqq : e ∈ B∪C → e ∉ Q'.biUnion triEdges :=
      fun he hq => disjoint_left.mp hQ'BC hq he
    have hbc : e ∈ Bc → e ∉ Yb := fun he hy => disjoint_left.mp hBankDis he hy
    have hce : e ∈ C → e ∈ edges H := fun he => hC he
    have hbe : e ∈ B → e ∈ edges H := fun he => hB he
    constructor
    · intro he
      obtain ⟨heE,heout⟩ := mem_sdiff.mp he
      have heQ : e ∉ Q'.biUnion triEdges := fun hh => heout (mem_union_left _ hh)
      have heBc : e ∉ Bc := fun hh => heout (mem_union_right _ hh)
      by_cases heC : e ∈ C
      · exact mem_union_left _ heC
      · by_cases heB : e ∈ B
        · rcases mem_union.mp (hBank ▸ heB) with hh | hh
          · exact False.elim (heBc hh)
          · exact mem_union_right _ (mem_union_right _ hh)
        · have hy : e ∈ Y := (Finset.ext_iff.mp hRem e).mp
            (mem_sdiff.mpr ⟨heE,fun hh => by
              rcases mem_union.mp hh with hh | hh
              · rcases mem_union.mp hh with hb' | hc'
                · exact heB hb'
                · exact heC hc'
              · exact heQ hh⟩)
          exact mem_union_right _ (mem_union_left _ hy)
    · intro he
      have heCases := mem_union.mp he
      rcases heCases with heC | heY
      · refine mem_sdiff.mpr ⟨hce heC,?_⟩
        intro hh
        rcases mem_union.mp hh with hq | hbc'
        · exact hqq (mem_union_right _ heC) hq
        · exact hcb heC (hBcB hbc')
      · rcases mem_union.mp heY with heY | heYb
        · have hy := mem_sdiff.mp ((Finset.ext_iff.mp hRem e).mpr heY)
          refine mem_sdiff.mpr ⟨hy.1,?_⟩
          intro hh
          rcases mem_union.mp hh with hq | hbc'
          · exact hy.2 (mem_union_right _ hq)
          · exact hy.2 (mem_union_left _ (mem_union_left _ (hBcB hbc')))
        · have heB : e ∈ B := hBank.symm ▸ mem_union_right _ heYb
          refine mem_sdiff.mpr ⟨hbe heB,?_⟩
          intro hh
          rcases mem_union.mp hh with hq | hbc'
          · exact hqq (mem_union_left _ heB) hq
          · exact hbc hbc' heYb

/-- Removing a SPECIFIED small mode from a dense basal reference and adding
an arbitrary new payload cannot create more holes than the removed mode.
The size of the added payload does not enter this upper bound. -/
theorem holes_after_replacement (E C Y₀ Y : Finset (Sym2 V)) (δ τ n : ℝ)
    (hRef : ∀ v, (degIn (E\(C∪Y₀)) v:ℝ) ≤ δ*n)
    (hMode : ∀ v, (degIn Y₀ v:ℝ) ≤ τ*n) :
    ∀ v, (degIn (E\(C∪Y)) v:ℝ) ≤ (δ+τ)*n := by
  intro v
  have hs : (E\(C∪Y)).filter (fun e => v ∈ e) ⊆
      (E\(C∪Y₀)).filter (fun e => v ∈ e) ∪ Y₀.filter (fun e => v ∈ e) := by
    intro e he
    obtain ⟨he,hv⟩ := mem_filter.mp he
    obtain ⟨heE,heout⟩ := mem_sdiff.mp he
    by_cases heY₀ : e ∈ Y₀
    · exact mem_union_right _ (mem_filter.mpr ⟨heY₀,hv⟩)
    · exact mem_union_left _ (mem_filter.mpr
        ⟨mem_sdiff.mpr ⟨heE,fun hh => by
          rcases mem_union.mp hh with hc | hy
          · exact heout (mem_union_left _ hc)
          · exact heY₀ hy⟩,hv⟩)
  have hc : (degIn (E\(C∪Y)) v:ℝ) ≤ degIn (E\(C∪Y₀)) v+degIn Y₀ v := by
    exact_mod_cast (card_le_card hs).trans (card_union_le _ _)
  nlinarith [hRef v,hMode v]

/-- Ambient physicality of a dense child upgrades to its OWN physical lattice.
The raw host indicator is not assumed physical. This pays the distinction
between lattice compatibility and available edges before seed exactification. -/
theorem intrinsic_dense_child (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∀ E : Finset (Sym2 V), E ⊆ edges H → IsPhysical H F E →
          (∀ v, (degIn (edges H\E) v:ℝ) ≤ η*Fintype.card V) →
          IsPhysical (subHost H E) F (edges (subHost H E)) := by
  obtain ⟨η,hη,n₀,hDel⟩ := sparse_edge_deletion_host α h hα
  refine ⟨η,hη,n₀,?_⟩
  intro V I _ H F hn h3 h4 E hE hPhys hsmall
  let B := edges H\E
  have hzero : ∀ e ∈ B, ind E e = 0 := by
    intro e he
    simp only [B,mem_sdiff] at he
    simp [ind,he.2]
  have hx := (hDel V I H F hn h3 h4 B hsmall (ind E)).mpr ⟨hPhys,hzero⟩
  have hDiff : edges H\B = E := by
    dsimp [B]
    ext e
    have hh : e ∈ E → e ∈ edges H := fun he => hE he
    simp only [mem_sdiff]
    tauto
  change ind (edges (subHost H E)) ∈ lattice (subHost H E) F
  rw [Residual.edges_subHost_eq hE]
  rwa [hDiff] at hx

end TypedTriangle.RawReference
