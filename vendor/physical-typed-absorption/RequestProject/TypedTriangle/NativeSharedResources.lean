/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeSharedCorePreparation
public import RequestProject.TypedTriangle.NativeProtectedStock
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
open CorePaid BasalIncidence SelSimul S07V40 S07V42 S07V43 S07V44

/-- Transport to the membership subtype without rewriting dependent
DecidablePred/Fintype instances. A conservative factor two suffices here. -/
lemma membership_core_geometry {V I : Type} [Fintype V] (H : Host V I)
    (F : Set (Multiset I)) (W : Finset V) {a : ℝ} {h : ℕ} (ha : 0 < a)
    (h3 : CommonNbrCond (restrictedHost H (univ\W)) F a)
    (h4 : HingeCond (restrictedHost H (univ\W)) F a h) :
    SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
      (H.lab ∘ Subtype.val) F (a/2) ∧
    SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
      (H.lab ∘ Subtype.val) F (a/2) h := by
  let f : {x // x ∈ W} → Survivors (univ\W) := fun x => ⟨x.1,by simpa using x.2⟩
  have hf : Function.Injective f := fun x y he =>
    Subtype.ext (congrArg (fun z : Survivors (univ\W) => z.1) he)
  have hrange : ∀ x : Survivors (univ\W), (∃ y, f y = x) ↔ x ∉ (∅ : Finset _) := by
    intro x
    constructor
    · simp
    · intro _
      exact ⟨⟨x.1,by simpa using x.2⟩,Subtype.ext rfl⟩
  have hg3 := commonNbr_deletion hf hrange ha h3 (δ := 0) (by simp) (by linarith)
  have hg4 := hinge_deletion hf hrange ha h4 (δ := 0) (h := h) (by simp) (by norm_num)
    (by simpa only [zero_mul] using (div_pos ha (by norm_num : (0:ℝ) < 2)).le)
  constructor
  · simpa only [SimpleGraph.comap,restrictedHost,Function.comp_def,f] using hg3
  · simpa only [SimpleGraph.comap,restrictedHost,Function.comp_def,f] using hg4

/-- Joint native preparation. Dimensions precede the number of colours;
degree caps precede the host. A previously fixed sparse basal terminal is
protected by the stock, selector AND bank. The bank is constructed after the
stock and selector, and the catalog is generated on its actual strata.
Only the later physical demand remains universally quantified. This result
does not assume a supplied stock, positive refiner or bank. -/
theorem native_shared_resources {I : Type} (F : Set (Multiset I))
    (α q0 C ξ : ℝ) (h : ℕ) (hα : 0 < α) (hq0 : 0 < q0) (hq1 : q0 ≤ 1)
    (hC : 1 ≤ C) (hξ : 0 < ξ) (hh : 6 ≤ h) :
    let β := α*q0^h/4
    ∃ d c E d' c' E' Ecell : ℕ, ∀ P : ℕ, ∀ εcap ρcap δcap : ℝ,
      0 < εcap → 0 < ρcap → 0 < δcap →
      ∃ κ ε ηT ρ κX τ : ℝ, 0 < κ ∧ 0 < ε ∧ ε ≤ εcap ∧
        0 < ηT ∧ 0 < ρ ∧ ρ ≤ ρcap ∧ 0 < κX ∧ 0 < τ ∧ τ ≤ ρcap ∧
        ∃ t n₀ : ℕ, Odd t ∧ 3 ≤ t ∧
        ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
          (T : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT : ℕ),
          n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
          CommonNbrCond H F α → HingeCond H F α h →
          IsDecomposition H F T DT → (∀ v, SparseEdge.degIn T v ≤ dT) →
          (dT:ℝ) ≤ ηT*Fintype.card V →
          ∃ (W : Finset V) (D : Finset (Finset V)) (R : Finset (Sym2 V)),
            q0*Fintype.card V/2 ≤ W.card ∧ (W.card:ℝ) < 2*q0*Fintype.card V ∧
            S07V45.CorePathContract H.G H.lab F W t ∧
            (∀ u v, H.G.Adj u v → |S07V48.sampW H.G H.lab F φ W u v/q0-1| ≤ ξ) ∧
            SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
              (H.lab ∘ Subtype.val) F β ∧
            SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
              (H.lab ∘ Subtype.val) F β h ∧
            IsDecomposition H F (cover D) D ∧ Disjoint (cover D) T ∧
            (∀ v, (SparseEdge.degIn (cover D) v:ℝ) < ρ*Fintype.card V) ∧
            (∀ u v, H.G.Adj u v → κX*Fintype.card V ≤ (good H F D u v).card) ∧
            Disjoint R (cover D∪T) ∧ Basal H F R ∧
            (∀ v, (edeg R v:ℝ) ≤ τ*Fintype.card V) ∧
            (∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
              ∃ Ps Y : Finset (Sym2 V), R∪L = Ps∪Y ∧ Disjoint Ps Y ∧ Basal H F Ps ∧
                (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
                (∀ v, (edeg Y v:ℝ) ≤ τ*Fintype.card V) ∧ IsPhysical H F Y) ∧
            ∃ (C0 : CoreCompression H.G H.lab F W d c E) (q z : ℕ),
              0 < q ∧ ε/4*W.card ≤ (q:ℝ) ∧
              (z:ℝ) ≤ δcap*W.card ∧
              (z:ℝ) ≤ coreDelta β h*W.card ∧
              (∀ Z : Finset V, Z.card ≤ z → Nonempty (DelCompression H.G H.lab F Z d' c' E')) ∧
              let Rc := catR β d c E d' c' E'
              let S := S07V47.protSetting C0 Rc P q Ecell z ((cover D∪R)∪T)
              let N := ⌊κ*(W.card:ℝ)^2⌋₊
              MacroBank S (Fintype.card (Cat d Rc)) N ∧
                Disjoint (Br S N) ((cover D∪R)∪T) ∧
                (∀ v, (deg (Br S N) v:ℝ) < ε*W.card) ∧
                ∀ j, CatalogGen C0 Rc (Zstrat S N j) := by
  let β := α*q0^h/4
  have hβ : 0 < β := by dsimp [β]; positivity
  obtain ⟨d,c,E,d',c',E',Ecell,hBank⟩ := native_protected_geometric_bank α β h hα hβ
  refine ⟨d,c,E,d',c',E',Ecell,?_⟩
  intro P εcap ρcap δcap hεcap hρcap hδcap
  have hδB : 0 < min δcap (coreDelta β h) :=
    lt_min hδcap (by unfold coreDelta; positivity)
  obtain ⟨κ,ε,η,hκ,hε,hεcap',hη,nB,hB⟩ :=
    hBank P εcap (min δcap (coreDelta β h)) hεcap hδB
  let τ := min (η*q0/16) ρcap
  have hτ : 0 < τ := lt_min (by positivity) hρcap
  obtain ⟨t,εS,δ,nS,ht,ht3,hεS,hδ,hPrep⟩ :=
    native_shared_core_positive_preparation α q0 τ C ξ h hα hq0 hq1 hτ hC hξ hh
  let ρ := min (δ/4) τ
  have hρ : 0 < ρ := lt_min (by positivity) hτ
  obtain ⟨εT,κX,hεT,hκX,nX,hStock⟩ := reserve_avoiding_basal F C α ρ h hC hα hρ
  let ηT := min (δ/4) (min εT τ)
  have hηT : 0 < ηT := lt_min (by positivity) (lt_min hεT hτ)
  let nCore := max nB (coreN0 β h)
  let n₀ := max nS (max nX (max ⌈4/δ⌉₊ ⌈2*nCore/q0⌉₊))
  refine ⟨κ,ε,ηT,ρ,κX,τ,hκ,hε,hεcap',hηT,hρ,
    (min_le_right _ _).trans (min_le_right _ _),hκX,hτ,min_le_right _ _,t,n₀,ht,ht3,?_⟩
  intro V _ H φ T DT dT hn hseed h2 h3 h4 hT hTd hTs
  have hnS : nS ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnX : nX ≤ Fintype.card V := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnδ : 4/δ ≤ (Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have hnC : 2*nCore/q0 ≤ (Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have hδn : 4 ≤ δ*Fintype.card V := by
    have hh' := (div_le_iff₀ hδ).mp hnδ
    nlinarith only [hh']
  obtain ⟨W,hWlow,hWhi,hCt,hraw,hc3,hc4,hWithdraw⟩ := hPrep H F φ h3 h4 h2 hseed hnS
  have hnW : nCore ≤ W.card := by
    have hc := (div_le_iff₀ hq0).mp hnC
    exact_mod_cast (show (nCore:ℝ) ≤ W.card by nlinarith only [hc,hWlow])
  obtain ⟨hg3,hg4⟩ := membership_core_geometry H F W
    (show 0 < α*q0^h/2 by positivity) hc3 hc4
  have hβeq : α*q0^h/2/2 = β := by dsimp [β]; ring
  rw [hβeq] at hg3 hg4
  obtain ⟨D,hD,hDT,hDd,hSupply⟩ := hStock H φ T DT dT hnX hseed h2 h3 h4 hT hTd
    (hTs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _))
      (by positivity)))
  let X := SimpleGraph.fromEdgeSet (cover D : Set (Sym2 V))
  let B := SimpleGraph.fromEdgeSet (T : Set (Sym2 V))
  letI : DecidableRel X.Adj := Classical.decRel _
  letI : DecidableRel B.Adj := Classical.decRel _
  letI : Fintype X.edgeSet := X.fintypeEdgeSet
  letI : Fintype B.edgeSet := B.fintypeEdgeSet
  have hDX : cover D ⊆ edges H := basal_subset_edges ⟨D,hD⟩
  have hTX : T ⊆ edges H := basal_subset_edges ⟨DT,hT⟩
  have hXmem (e : Sym2 V) : e ∈ X.edgeSet ↔ e ∈ cover D := by
    simp only [X,SimpleGraph.edgeSet_fromEdgeSet,Set.mem_sdiff,mem_coe,Sym2.mem_diagSet]
    exact ⟨And.left,fun he => ⟨he,edges_diagonal_free hDX e he⟩⟩
  have hBmem (e : Sym2 V) : e ∈ B.edgeSet ↔ e ∈ T := by
    simp only [B,SimpleGraph.edgeSet_fromEdgeSet,Set.mem_sdiff,mem_coe,Sym2.mem_diagSet]
    exact ⟨And.left,fun he => ⟨he,edges_diagonal_free hTX e he⟩⟩
  let r := ⌈ρ*Fintype.card V⌉₊
  have hr : (r:ℝ) ≤ δ*Fintype.card V := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ ρ*Fintype.card V by positivity)
    have hρδ : ρ ≤ δ/4 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hρδ (show (0:ℝ) ≤ Fintype.card V by positivity)]
  have hb : (dT:ℝ) ≤ δ*Fintype.card V := hTs.trans
    (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (by linarith : δ/4 ≤ δ)) (by positivity))
  have hXd : ∀ v, X.degree v ≤ r := by
    intro v
    have hd := fromEdges_degree_le _ (edges_diagonal_free hDX) (r := r) (fun v => by
      exact_mod_cast (hDd v).le.trans (Nat.le_ceil _)) v
    convert hd using 1 <;> congr 2 <;> apply Subsingleton.elim
  have hBd : ∀ v, B.degree v ≤ dT := by
    intro v
    have hd := fromEdges_degree_le _ (edges_diagonal_free hTX) hTd v
    convert hd using 1 <;> congr 2 <;> apply Subsingleton.elim
  obtain ⟨R,hRdis,hR,hRd,hMode⟩ := hWithdraw X B r dT (fromEdges_le_host hDX) hXd hBd hr hb
  have hRdis' : Disjoint R (cover D∪T) := by
    apply disjoint_left.mpr
    intro e heR he
    apply disjoint_left.mp hRdis heR
    rcases mem_union.mp he with he | he
    · apply mem_union_left
      simpa only [SimpleGraph.mem_edgeFinset] using (hXmem e).mpr he
    · apply mem_union_right
      simpa only [SimpleGraph.mem_edgeFinset] using (hBmem e).mpr he
  have hMode' : ∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
      ∃ Ps Y : Finset (Sym2 V), R∪L = Ps∪Y ∧ Disjoint Ps Y ∧ Basal H F Ps ∧
        (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
        (∀ v, (edeg Y v:ℝ) ≤ τ*Fintype.card V) ∧ IsPhysical H F Y := by
    intro L hL hphys
    apply hMode L ?_ hphys
    intro e he
    simpa only [SimpleGraph.mem_edgeFinset] using (hXmem e).mpr (hL he)
  obtain ⟨C0,q,z,hq,hql,hz',hCZ,hMake⟩ := hB H F W
    ((le_max_left _ _).trans hnW) h3 h4 hg3 hg4
  have hzcap : (z:ℝ) ≤ δcap*W.card := hz'.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hz : (z:ℝ) ≤ coreDelta β h*W.card := hz'.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  have hF0 : ∀ v, (degIn ((cover D∪R)∪T) v:ℝ) ≤ η*W.card := by
    intro v
    have hu : (degIn ((cover D∪R)∪T) v:ℝ) ≤
        degIn (cover D) v + degIn R v + degIn T v := by
      have ha := edeg_union_le (cover D∪R) T v
      have hb' := edeg_union_le (cover D) R v
      change degIn ((cover D∪R)∪T) v ≤ degIn (cover D∪R) v+degIn T v at ha
      change degIn (cover D∪R) v ≤ degIn (cover D) v+degIn R v at hb'
      exact_mod_cast (show degIn ((cover D∪R)∪T) v ≤
        degIn (cover D) v+degIn R v+degIn T v by omega)
    have hx := (hDd v).le
    have hr' := hRd v
    change (degIn (cover D) v:ℝ) ≤ ρ*Fintype.card V at hx
    change (degIn R v:ℝ) ≤ τ*Fintype.card V at hr'
    have ht' : (degIn T v:ℝ) ≤ ηT*Fintype.card V :=
      (show (degIn T v:ℝ) ≤ dT by exact_mod_cast hTd v).trans hTs
    have hρτ : ρ ≤ τ := min_le_right _ _
    have hητ : ηT ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
    have hτlow : τ ≤ η*q0/16 := min_le_left _ _
    have h1 := mul_le_mul_of_nonneg_right hρτ (show (0:ℝ) ≤ Fintype.card V by positivity)
    have h2' := mul_le_mul_of_nonneg_right hητ (show (0:ℝ) ≤ Fintype.card V by positivity)
    have h3' := mul_le_mul_of_nonneg_right hτlow (show (0:ℝ) ≤ Fintype.card V by positivity)
    have h4' := mul_le_mul_of_nonneg_left hWlow hη.le
    nlinarith only [hu,hx,hr',ht',h1,h2',h3',h4',hWlow,
      mul_nonneg hη.le (show (0:ℝ) ≤ W.card by positivity)]
  obtain ⟨hM,hBankDis,hBankDeg⟩ := hMake ((cover D∪R)∪T) hF0
  have hcat := catalogGen_on_protected_strata hβ hg3 hg4 ((le_max_right _ _).trans hnW)
    C0 hz hCZ ((cover D∪R)∪T) hM
  exact ⟨W,D,R,hWlow,hWhi,hCt,hraw,hg3,hg4,hD,hDT,hDd,hSupply,hRdis',hR,hRd,hMode',
    C0,q,z,hq,hql,hzcap,hz,hCZ,hM,hBankDis,hBankDeg,hcat⟩

end TypedTriangle.CatalogNative
