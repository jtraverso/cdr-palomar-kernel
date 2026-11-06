/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexPreparedWindowResources
public import RequestProject.TypedTriangle.VortexNestedH4Transport
public import RequestProject.TypedTriangle.NativeProtectedGeometricBankEarlyProtection
public import RequestProject.TypedTriangle.ProtectedAllocationCatalog
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000

namespace TypedTriangle.Vortex
open CatalogNative S07V40 S07V42 S07V43 S07V44

/-- The prepared nested core is exactly the fixed vertex window needed by
the protected geometric bank and its catalogs. The protected edge set can be
the union of the old stock, completion stock and physical selector. -/
theorem bank_on_prepared_fixed_window_early_protection (α β : ℝ) (h : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    ∃ d c E d' c' E' Ecell : ℕ, ∃ η : ℝ, 0 < η ∧
      ∀ P : ℕ, ∀ εcap δcap : ℝ, 0 < εcap → 0 < δcap →
      ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ ε ≤ εcap ∧
      ∃ n₀ : ℕ,
        ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
          (W : Finset V) (A : Finset (Survivors (univ \ W)))
          (F0 : Finset (Sym2 V)),
          n₀ ≤ (W \ liftVertexSet (univ \ W) A).card →
          CommonNbrCond H F α → HingeCond H F α h →
          CommonNbrCond (restrictedHost (restrictedHost H (univ \ W)) A) F β →
          HingeCond (restrictedHost (restrictedHost H (univ \ W)) A) F β h →
          (∀ v, (degIn F0 v : ℝ) ≤ η * (W \ liftVertexSet (univ \ W) A).card) →
          ∃ (C0 : CoreCompression H.G H.lab F
                (W \ liftVertexSet (univ \ W) A) d c E) (qm z : ℕ),
            0 < qm ∧ ε/4*(W \ liftVertexSet (univ \ W) A).card ≤ (qm:ℝ) ∧
            (z:ℝ) ≤ δcap*(W \ liftVertexSet (univ \ W) A).card ∧
            (∀ Z : Finset V, Z.card ≤ z →
              Nonempty (DelCompression H.G H.lab F Z d' c' E')) ∧
            let Rc := catR β d c E d' c' E'
            let Setting := S07V47.protSetting C0 Rc P qm Ecell z F0
            let M := ⌊κ*((W \ liftVertexSet (univ \ W) A).card:ℝ)^2⌋₊
            MacroBank Setting (Fintype.card (Cat d Rc)) M ∧
              Disjoint (Br Setting M) F0 ∧
              (∀ v, (deg (Br Setting M) v:ℝ) <
                ε*(W \ liftVertexSet (univ \ W) A).card) ∧
              ∀ j, CatalogGen C0 Rc (Zstrat Setting M j) := by
  obtain ⟨d,c,E,d',c',E',Ecell,η,hη,hBank⟩ :=
    native_protected_geometric_bank_early_protection α β h hα hβ
  refine ⟨d,c,E,d',c',E',Ecell,η,hη,?_⟩
  intro P εcap δcap hεcap hδcap
  have hδB : 0 < min δcap (coreDelta β h) :=
    lt_min hδcap (by unfold coreDelta; positivity)
  obtain ⟨κ,ε,hκ,hε,hεcap,nB,hMake⟩ :=
    hBank P εcap (min δcap (coreDelta β h)) hεcap hδB
  refine ⟨κ,ε,hκ,hε,hεcap,max nB (coreN0 β h),?_⟩
  intro V I _ H F W A F0 hn h3 h4 h3A h4A hF0
  let W' := W \ liftVertexSet (univ \ W) A
  have hnB : nB ≤ W'.card := (le_max_left _ _).trans hn
  have hnCore : coreN0 β h ≤ W'.card := (le_max_right _ _).trans hn
  have hc3 : SparseEdge.CommonNbrCond
      (H.G.comap (Subtype.val : {x // x ∈ W'} → V))
      (H.lab ∘ Subtype.val) F β :=
    nested_prepared_commonNbrCond_direct H F W A β h3A
  have hc4 : SparseEdge.HingeCond
      (H.G.comap (Subtype.val : {x // x ∈ W'} → V))
      (H.lab ∘ Subtype.val) F β h :=
    nested_prepared_hingeCond_direct H F W A β h h4A
  obtain ⟨C0,qm,z,hqm,hqlo,hz',hCZ,hProtected⟩ :=
    hMake H F W' hnB h3 h4 hc3 hc4
  have hzcap : (z:ℝ) ≤ δcap*W'.card := hz'.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hzcore : (z:ℝ) ≤ coreDelta β h*W'.card := hz'.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  obtain ⟨hM,hDis,hDeg⟩ := hProtected F0 hF0
  have hCat := catalogGen_on_protected_strata hβ hc3 hc4 hnCore C0
    hzcore hCZ F0 hM
  exact ⟨C0,qm,z,hqm,hqlo,hzcap,hCZ,hM,hDis,hDeg,hCat⟩

#print axioms bank_on_prepared_fixed_window_early_protection

end TypedTriangle.Vortex
