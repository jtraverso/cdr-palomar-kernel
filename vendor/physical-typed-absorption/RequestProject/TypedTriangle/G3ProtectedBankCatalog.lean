/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3ProtectedBudget
public import RequestProject.TypedTriangle.ProtectedAllocationCatalog
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
namespace TypedTriangle.CatalogNative
open S07V40 S07V42 S07V43 S07V44

/-- Build the physical bank and every protected-stratum catalog on the SAME
core W after an old stock S, a new reserve D, and a positive selector R have
been fixed.  The old stock is charged only through its own geometric window.
This is a conditional resource assembler; producing S,D,R with the required
windows from H1--H4 is the separate preparation obligation. -/
theorem protected_bank_catalog_for_three_resources (α β : ℝ) (h : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    ∃ d c E d' c' E' Ecell : ℕ,
      ∀ P : ℕ, ∀ εcap δcap : ℝ, 0 < εcap → 0 < δcap →
      ∃ κ ε η : ℝ, 0 < κ ∧ 0 < ε ∧ ε ≤ εcap ∧ 0 < η ∧
      ∃ n₀ : ℕ,
        ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
          (W : Finset V) (S D R : Finset (Sym2 V)) (q θ ρ τ : ℝ),
          n₀ ≤ W.card → CommonNbrCond H F α → HingeCond H F α h →
          SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
            (H.lab ∘ Subtype.val) F β →
          SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
            (H.lab ∘ Subtype.val) F β h →
          q*Fintype.card V/2 ≤ W.card → θ+ρ+τ ≤ η*q/2 →
          (∀ v, (SparseEdge.degIn S v:ℝ) ≤ θ*Fintype.card V) →
          (∀ v, (SparseEdge.degIn D v:ℝ) ≤ ρ*Fintype.card V) →
          (∀ v, (SparseEdge.degIn R v:ℝ) ≤ τ*Fintype.card V) →
          ∃ (C0 : CoreCompression H.G H.lab F W d c E) (qm z : ℕ),
            0 < qm ∧ ε/4*W.card ≤ (qm:ℝ) ∧
            (z:ℝ) ≤ δcap*W.card ∧
            (∀ Z : Finset V, Z.card ≤ z →
              Nonempty (DelCompression H.G H.lab F Z d' c' E')) ∧
            let Rc := catR β d c E d' c' E'
            let F0 := (S∪D)∪R
            let Setting := S07V47.protSetting C0 Rc P qm Ecell z F0
            let N := ⌊κ*(W.card:ℝ)^2⌋₊
            MacroBank Setting (Fintype.card (Cat d Rc)) N ∧
              Disjoint (Br Setting N) F0 ∧
              (∀ v, (deg (Br Setting N) v:ℝ) < ε*W.card) ∧
              ∀ j, CatalogGen C0 Rc (Zstrat Setting N j) := by
  obtain ⟨d,c,E,d',c',E',Ecell,hBank⟩ :=
    native_protected_geometric_bank α β h hα hβ
  refine ⟨d,c,E,d',c',E',Ecell,?_⟩
  intro P εcap δcap hεcap hδcap
  have hδB : 0 < min δcap (coreDelta β h) :=
    lt_min hδcap (by unfold coreDelta; positivity)
  obtain ⟨κ,ε,η,hκ,hε,hεcap,hη,nB,hMake⟩ :=
    hBank P εcap (min δcap (coreDelta β h)) hεcap hδB
  refine ⟨κ,ε,η,hκ,hε,hεcap,hη,max nB (coreN0 β h),?_⟩
  intro V I _ H F W S D R q θ ρ τ hn h3 h4 hc3 hc4 hW hSum hS hD hR
  have hnB : nB ≤ W.card := (le_max_left _ _).trans hn
  have hnC : coreN0 β h ≤ W.card := (le_max_right _ _).trans hn
  obtain ⟨C0,qm,z,hqm,hqlo,hz',hCZ,hProtected⟩ :=
    hMake H F W hnB h3 h4 hc3 hc4
  have hzcap : (z:ℝ) ≤ δcap*W.card := hz'.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hzcore : (z:ℝ) ≤ coreDelta β h*W.card := hz'.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  let F0 := (S∪D)∪R
  have hF0 := protected_bank_cap_of_three_resources W S D R q θ ρ τ η
    hW hSum hη.le hS hD hR
  obtain ⟨hM,hDis,hDeg⟩ := hProtected F0 hF0
  have hCat := catalogGen_on_protected_strata hβ hc3 hc4 hnC C0
    hzcore hCZ F0 hM
  exact ⟨C0,qm,z,hqm,hqlo,hzcap,hCZ,hM,hDis,hDeg,hCat⟩

end TypedTriangle.CatalogNative
