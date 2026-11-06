/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeChildBank
public import RequestProject.TypedTriangle.ProtectedMacroBank
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
open S07V42 S07V43 S07V40 ProtectedBank

/-- Prepare the physical charge bank AROUND an external protected edge set.
The ambient lattice and the same true core remain fixed. External protection
is paid in the native cell's degree window, not an additional supply premise. -/
theorem native_protected_child_bank (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β)
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
        ∀ P q zmax N b0 : ℕ, 0 < q →
        (zmax:ℝ) ≤ δ*W.card →
        ((b0+q+(childSetting C0 (catR β d c E d' c' E') P q Ecell zmax).Bstar*Ecell:ℕ):ℝ) ≤ ε*W.card →
        (∀ Z : Finset V, Z.card ≤ zmax → DelCompression H.G H.lab F Z d' c' E') →
        2*Ecell*(childSetting C0 (catR β d c E d' c' E') P q Ecell zmax).Bstar*N ≤ q*zmax →
        ∀ F0 : Finset (Sym2 V), (∀ v, degIn F0 v ≤ b0) →
        let S := childSetting C0 (catR β d c E d' c' E') P q Ecell zmax
        MacroBank (protect S F0) (Fintype.card (Cat d (catR β d c E d' c' E'))) N ∧
          Disjoint (Br (protect S F0) N) F0 := by
  obtain ⟨Ecell,ε,δ,hε,hδ,n₀,hCell⟩ := native_catalog_cell α β h hα hβ d c E d' c' E'
  refine ⟨Ecell,ε,min δ (coreDelta β h),hε,
    lt_min hδ (by unfold coreDelta; positivity),n₀,?_⟩
  intro V I _ H F W h3 h4 hc3 hc4 hnC hn C0 P q zmax N b0 hq hz hbud CZ hcap F0 hF0
  let S := childSetting C0 (catR β d c E d' c' E') P q Ecell zmax
  have hzδ : (zmax:ℝ) ≤ δ*W.card := hz.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hzcore : (zmax:ℝ) ≤ coreDelta β h*W.card := hz.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  have hSup : CellSupply (protect S F0) := by
    intro B Z hB hZ l hl
    have hl' : S.g l.2.1 ∈ S.K Z := hl
    have hlRaw := (childSetting_g_mem_K_iff C0 (catR β d c E d' c' E')
      P q Ecell zmax l.2.1 Z).mp hl'
    have hbU : ∀ v, degIn (B∪F0) v ≤ b0+q+S.Bstar*Ecell := by
      intro v
      have hh : degIn (B∪F0) v ≤ degIn B v+degIn F0 v := by
        unfold degIn
        rw [filter_union]
        exact card_union_le _ _
      have hb := hB v
      have hf := hF0 v
      change degIn B v ≤ q+S.Bstar*Ecell at hb
      omega
    obtain ⟨A,Y,hA,hDis,hAv,hYE,hcard,hcharge⟩ := hCell H F W h3 h4 hc3 hc4 hnC hn C0 Z
      ((Nat.cast_le.mpr hZ).trans hzδ) (CZ Z hZ) (B∪F0) (b0+q+S.Bstar*Ecell)
      hbU hbud l.2.1 hlRaw l.1
    have hGood : GoodCell S (B∪F0) Z l ⟨A,Y⟩ := by
      refine ⟨hA.1,hA.2.1,hA.2.2,hDis,hAv,hcard,?_⟩
      show charge (tagW H.G H.lab F W) Y =
        sgnQ l.1 ((gCat C0 (catR β d c E d' c' E') l.2.1,0) : ClassQ H.G H.lab F W × ℤ)
      rw [charge_tagW_eq_sgnQ_iff]
      refine ⟨?_,fun e he => edge_child_of_deleted (hYE e he)⟩
      rw [hcharge]
      rfl
    exact ⟨⟨A,Y⟩,goodCell_protect (S:=S) F0 B Z l _ hGood⟩
  have hM : MacroBank (protect S F0)
      (Fintype.card (Cat d (catR β d c E d' c' E'))) N :=
    macro_bank hq hSup (protect_basal F0 (childSetting_basal C0 _ P q Ecell zmax))
      (childSetting_chainBound hβ hc3 hc4 hnC C0 P q Ecell zmax hzcore CZ) hcap
  exact ⟨hM,protected_bank_disjoint F0 hM⟩

end TypedTriangle.CatalogNative
