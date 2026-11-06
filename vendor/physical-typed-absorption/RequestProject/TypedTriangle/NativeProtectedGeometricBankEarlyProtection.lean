/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeProtectedChildBank
public import RequestProject.TypedTriangle.NativeCatalogCompression
public import RequestProject.TypedTriangle.QuadraticBankBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
open S07V42 S07V43 S07V40 ProtectedBank

/-- Original ambient/core geometry constructs a quadratic charge bank that
avoids ANY externally protected edge set in a fixed positive degree window.
The compression and charges refer to the original host throughout. Dimensions
and cell size precede arbitrary positive degree/deletion caps; all numerical
budgets precede both the host and its protected set. -/
theorem native_protected_geometric_bank_early_protection (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ d c E d' c' E' Ecell : ℕ, ∃ η : ℝ, 0 < η ∧ ∀ P : ℕ, ∀ εcap δcap : ℝ, 0 < εcap → 0 < δcap →
      ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ ε ≤ εcap ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        n₀ ≤ W.card → CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        ∃ C0 : CoreCompression H.G H.lab F W d c E, ∃ q z : ℕ,
          0 < q ∧ ε/4*W.card ≤ (q:ℝ) ∧ (z:ℝ) ≤ δcap*W.card ∧
          (∀ Z : Finset V, Z.card ≤ z → Nonempty (DelCompression H.G H.lab F Z d' c' E')) ∧
          ∀ F0 : Finset (Sym2 V), (∀ v, (degIn F0 v:ℝ) ≤ η*W.card) →
          let S := childSetting C0 (catR β d c E d' c' E') P q Ecell z
          let N := ⌊κ*(W.card:ℝ)^2⌋₊
          MacroBank (protect S F0) (Fintype.card (Cat d (catR β d c E d' c' E'))) N ∧
            Disjoint (Br (protect S F0) N) F0 ∧
            ∀ v, (deg (Br (protect S F0) N) v:ℝ) < ε*W.card := by
  obtain ⟨d,c,E,d',c',E',δc,hδc,nc,hCmp⟩ := native_all_catalog_compressions α β h hα hβ
  obtain ⟨Ecell,εb,δb,hεb,hδb,nb,hBank⟩ := native_protected_child_bank α β h hα hβ d c E d' c' E'
  refine ⟨d,c,E,d',c',E',Ecell,εb/2,by positivity,?_⟩
  intro P εcap δcap hεcap hδcap
  let ε := min (εb/2) εcap
  have hε : 0 < ε := lt_min (by positivity) hεcap
  let δ := min δc (min δb δcap)
  have hδ : 0 < δ := lt_min hδc (lt_min hδb hδcap)
  let B := 2*Fintype.card (Cat d (catR β d c E d' c' E'))*P
  obtain ⟨κ,hκ,nq,hBudget⟩ := quadratic_bank_budget ε δ Ecell B hε hδ
  refine ⟨κ,ε,hκ,hε,min_le_right _ _,
    max nc (max nb (max (coreN0 β h) nq)),?_⟩
  intro V I _ H F W hn h3 h4 hc3 hc4
  have hnc : nc ≤ W.card := (le_max_left _ _).trans hn
  have hnb : nb ≤ W.card := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnCore : coreN0 β h ≤ W.card :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnq : nq ≤ W.card :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  obtain ⟨⟨C0⟩,hCZ⟩ := hCmp H F W hnc h3 h4 hc3 hc4
  obtain ⟨q,z,hq,hz,hdegree,hcap,hql⟩ := hBudget W.card hnq
  have hzC : (z:ℝ) ≤ δc*W.card := hz.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hzB : (z:ℝ) ≤ δb*W.card := hz.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by positivity))
  have hzCap : (z:ℝ) ≤ δcap*W.card := hz.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by positivity))
  let CZ : ∀ Z : Finset V, Z.card ≤ z → DelCompression H.G H.lab F Z d' c' E' :=
    fun Z hZ => Classical.choice (hCZ Z ((Nat.cast_le.mpr hZ).trans hzC))
  refine ⟨C0,q,z,hq,hql,hzCap,fun Z hZ => ⟨CZ Z hZ⟩,?_⟩
  intro F0 hF0
  let b0 := ⌊(εb/2)*W.card⌋₊
  have hb0 : ∀ v, degIn F0 v ≤ b0 := fun v => Nat.le_floor (hF0 v)
  have hb0R : (b0:ℝ) ≤ (εb/2)*W.card := Nat.floor_le (by positivity)
  have hdegreeHalf : ((q+B*Ecell:ℕ):ℝ) ≤ (εb/2)*W.card := hdegree.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hbudget : ((b0+q+B*Ecell:ℕ):ℝ) ≤ εb*W.card := by
    push_cast at hdegreeHalf ⊢
    linarith
  obtain ⟨hM,hDis⟩ := hBank H F W h3 h4 hc3 hc4 hnCore hnb C0 P q z
    ⌊κ*(W.card:ℝ)^2⌋₊ b0 hq hzB hbudget CZ hcap F0 hb0
  refine ⟨hM,hDis,?_⟩
  intro v
  exact (show (deg (Br (protect (childSetting C0 (catR β d c E d' c' E') P q Ecell z) F0)
    ⌊κ*(W.card:ℝ)^2⌋₊) v:ℝ) < (q+B*Ecell:ℕ) by exact_mod_cast hM.maxdeg v).trans_le hdegree

#print axioms native_protected_geometric_bank_early_protection

end TypedTriangle.CatalogNative
