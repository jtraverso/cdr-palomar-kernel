/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeCatalogCell
public import RequestProject.S07V43.ChildSetting
public import RequestProject.S07V40.MacroBank
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
open S07V42 S07V43

/-- A native child-tagged bank constructor with explicit numerical budgets.
Every payload is forced into the child by the non-child edge-count coordinate. The cell supply
is constructed by G2; it is not a premise. Compression data are the precise
exports discharged separately by native_catalog_compressions. -/
theorem native_child_bank (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (d c E d' c' E' : ℕ) :
    ∃ Ecell : ℕ, ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        coreN0 β h ≤ W.card → n₀ ≤ W.card →
        ∀ C0 : CoreCompression H.G H.lab F W d c E,
        ∀ P q zmax N : ℕ, 0 < q →
        (zmax:ℝ) ≤ δ*W.card →
        ((q+(childSetting C0 (catR β d c E d' c' E') P q Ecell zmax).Bstar*Ecell:ℕ):ℝ) ≤ ε*W.card →
        (∀ Z : Finset V, Z.card ≤ zmax → DelCompression H.G H.lab F Z d' c' E') →
        2*Ecell*(childSetting C0 (catR β d c E d' c' E') P q Ecell zmax).Bstar*N ≤ q*zmax →
        S07V40.MacroBank (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax)
          (Fintype.card (Cat d (catR β d c E d' c' E'))) N := by
  obtain ⟨Ecell,ε,δ,hε,hδ,n₀,hCell⟩ := native_catalog_cell α β h hα hβ d c E d' c' E'
  refine ⟨Ecell,ε,min δ (coreDelta β h),hε,
    lt_min hδ (by unfold coreDelta; positivity),n₀,?_⟩
  intro V I _ H F W h3 h4 hc3 hc4 hnC hn C0 P q zmax N hq hz hbud CZ hcap
  let S := childSetting C0 (catR β d c E d' c' E') P q Ecell zmax
  have hzδ : (zmax:ℝ) ≤ δ*W.card := hz.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hzcore : (zmax:ℝ) ≤ coreDelta β h*W.card := hz.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  have hSup : S07V40.CellSupply S := by
    intro B Z hB hZ l hl
    rw [childSetting_g_mem_K_iff] at hl
    obtain ⟨A,Y,hA,hDis,hAv,hYE,hcard,hcharge⟩ := hCell H F W h3 h4 hc3 hc4 hnC hn C0 Z
      ((Nat.cast_le.mpr hZ).trans hzδ) (CZ Z hZ) B (q+S.Bstar*Ecell)
      (fun v => hB v) hbud l.2.1 hl l.1
    refine ⟨⟨A,Y⟩,hA.1,hA.2.1,hA.2.2,hDis,hAv,hcard,?_⟩
    show S07V40.charge (tagW H.G H.lab F W) Y =
      S07V40.sgnQ l.1 ((gCat C0 (catR β d c E d' c' E') l.2.1,0) : ClassQ H.G H.lab F W × ℤ)
    rw [charge_tagW_eq_sgnQ_iff]
    refine ⟨?_,fun e he => edge_child_of_deleted (hYE e he)⟩
    rw [hcharge]
    rfl
  exact S07V40.macro_bank hq hSup (childSetting_basal C0 _ P q Ecell zmax)
    (childSetting_chainBound hβ hc3 hc4 hnC C0 P q Ecell zmax hzcore CZ) hcap
end TypedTriangle.CatalogNative
