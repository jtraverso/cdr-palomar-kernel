module
public import RequestProject.TypedTriangle.PaschRawStockWithdrawalUniformProfile
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SimpleGraph SelSimul SelBridge SelTyped S07V26 S07V27
open TypedTriangle.ComponentRows S07V24 S07V25 S07V45
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch

/-- The raw profile and future-edge caps are chosen before the routing and
core-pool rates. The same sampled stock and literal weighted withdrawal are
retained; only the terminal forbidden cap is selected after those rates. -/
theorem raw_stock_weighted_withdrawal_uniform_rich {I : Type} (F : Set (Multiset I))
    (aa bb α ζ a : ℝ) (h qTests m : ℕ)
    (hζ : 0 < ζ) (haa : 0 < aa) (hab : aa≤bb) (hα : 0 < α)
    (ha : 0 < a)
    (hm : 0 < m) (hOdd : Odd (m+1)) :
    ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧
      ∀ qRate κGeom : ℝ, 0 < qRate → 0 < κGeom →
      ∃ θ : ℝ, 0 < θ ∧ ∀ τ ρcap δStock : ℝ, 0 < τ → 0 < ρcap → 0 < δStock →
      ∃ ρ κStock : ℝ, 0 < ρ ∧ ρ≤ρcap ∧ 0 < κStock ∧ ∃ N : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (μ : Finset V→ℝ)
        (W : Finset V) (T S : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT dS : ℕ),
        N≤Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        (∀ Q, IsAllowed H F Q → aa/Fintype.card V≤μ Q ∧ μ Q≤bb/Fintype.card V) →
        (∀ e∈edges H, |bdry H F μ e-1|≤ε) →
        T⊆edges H → IsDecomposition H F T DT → Disjoint T S →
        (∀ v, degIn T v≤dT) → (dT : ℝ)≤θ*Fintype.card V →
        (∀ v, degIn S v≤dS) → (dS : ℝ)≤γ*Fintype.card V →
        2≤qRate*Fintype.card V → (W.card : ℝ)≤2*qRate*Fintype.card V →
        qRate*Fintype.card V/4≤(W.card : ℝ) →
        (∀ v x y, OrigAdm H.G H.lab F v x y →
          a*(Fintype.card V : ℝ)^m*qRate^m/4≤
            (pathsIn (link H.G H.lab F v) m x y W).card) →
        (∀ u v, u≠v → ∀ k, ({H.lab u,H.lab v,k} : Multiset I)∈F →
          κGeom*Fintype.card V≤((TypedTriangle.commonNbrs H k u v)∩W).card) →
        ∀ (Ambient : Type) [Fintype Ambient] (ι : V ↪ Ambient)
          (Rprev : Finset (Finset Ambient)) (Lprev : ℕ), PairCodegreeBound Rprev Lprev →
        ∀ (ν : Type) [Fintype ν] (Xtests : ℕ→ν→Finset (Finset V)→ℝ),
          Fintype.card ν≤(Fintype.card V)^qTests →
          (∀ ℓ, 1≤ℓ → ℓ≤4 → ∀ k U, 0≤Xtests ℓ k U) →
        ∃ (Praw D : Finset (Finset V)) (qSel : ℕ),
          CommonNbrCond (residual H (T∪S)) F (α/2) ∧
          (∀ e∈edges (residual H (T∪S)),
            |bdry (residual H (T∪S)) F μ e-1|≤BasalIncidence.rawStockProfileMargin α) ∧
          Praw⊆allowed (residual H (T∪S)) F ∧ IsPacking (residual H (T∪S)) F Praw ∧
          D⊆Praw ∧ IsDecomposition H F (BasalIncidence.cover D) D ∧
          Disjoint (BasalIncidence.cover D) (T∪S) ∧
          (∀ v, (degIn (BasalIncidence.cover D) v : ℝ) < ρ*Fintype.card V) ∧
          (∀ u v, H.G.Adj u v → κStock*Fintype.card V≤(BasalIncidence.good H F D u v).card) ∧
          (count D : ℝ)≤δStock*(Fintype.card V : ℝ)^2 ∧
          (∑ Q∈D, childPaddedWeight ι Rprev Lprev Q)≤(1+ζ)*bb*Fintype.card V ∧
          (∀ ℓ, 1≤ℓ → ℓ≤4 → ∀ k : ν,
            floorTupleTestControl (allowed (residual H (T∪S)) F)
              (fun Q => μ Q/(1+BasalIncidence.rawStockProfileMargin α)) Praw (Xtests ℓ k) ℓ) ∧
          let X := SimpleGraph.fromEdgeSet (BasalIncidence.cover D : Set (Sym2 V))
          let B := SimpleGraph.fromEdgeSet (T : Set (Sym2 V))
          let r := ⌈ρ*Fintype.card V⌉₊
          qSel≤CorePaid.Explicit.selQLimit (Vortex.windowRouteRate a qRate m) (selA (m+1))*
            (3*r+forkQ κGeom r+4+1) ∧
          WeightedWithdrawalResult ι H F a κGeom m W X B r (selA (m+1)) qSel τ
            (Rprev∪mapConfiguration ι D) (Lprev+1) := by
  obtain ⟨θRaw,ε,γ,hθRaw,hε,hγ,hStock⟩ :=
    BasalIncidence.reserve_from_raw_profile_with_pasch_ambient_and_tuple_tests
      F aa bb α ζ h qTests hζ haa hab hα
  refine ⟨ε,γ,hε,hγ,?_⟩
  intro qRate κGeom hqRate hκGeom
  have hθW := (weightedWithdrawal_budgets_pos m hκGeom hqRate ha (show (0 : ℝ) < 1 by norm_num)).1
  refine ⟨min θRaw (weightedWithdrawalStockBudget κGeom qRate a m),
    lt_min hθRaw hθW,?_⟩
  intro τ ρcap δStock hτ hρcap hδStock
  let δ := weightedWithdrawalInputBudget κGeom qRate a m τ
  have hδ : 0 < δ := (weightedWithdrawal_budgets_pos m hκGeom hqRate ha hτ).2
  let ρ := min ρcap (δ/4)
  have hρ : 0 < ρ := lt_min hρcap (by positivity)
  obtain ⟨κStock,hκStock,nStock,hStockHost⟩ := hStock ρ δStock hρ hδStock
  let nWithdrawal := weightedWithdrawalOrder κGeom qRate a m τ
  refine ⟨ρ,κStock,hρ,min_le_left _ _,hκStock,
    max nStock (max nWithdrawal ⌈2/δ⌉₊),?_⟩
  intro V _ H μ W T S DT dT dS hn h3 h4 hμ hLoad hT hDT hTS hdT hTcap hdS hScap
    hOrder hWindow hWindowLower hPaths hPool Ambient _ ι Rprev Lprev hCodeg ν _ Xtests hν hTests
  have hnStock : nStock≤Fintype.card V := (le_max_left _ _).trans hn
  have hnWithdrawal : nWithdrawal≤Fintype.card V := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hδn : 2≤δ*Fintype.card V := by
    have hc : ⌈2/δ⌉₊≤Fintype.card V := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    have hh := (Nat.le_ceil (2/δ)).trans (Nat.cast_le.mpr hc)
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hh
  have hTRaw : (dT : ℝ)≤θRaw*Fintype.card V :=
    hTcap.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hTW : (dT : ℝ)≤weightedWithdrawalStockBudget κGeom qRate a m*Fintype.card V :=
    hTcap.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  obtain ⟨Praw,D,hStockH3,hStockLoad,hPsub,hPraw,_,hDP,hD,hAvoid,hDd,hSupply,hCount,hAmbient,hControls⟩ :=
    hStockHost H μ T S DT dT dS hnStock h3 h4 hμ hLoad hT hDT hTS hdT hTRaw hdS hScap
      Ambient ι Rprev Lprev hCodeg ν Xtests hν hTests
  let X := SimpleGraph.fromEdgeSet (BasalIncidence.cover D : Set (Sym2 V))
  let B := SimpleGraph.fromEdgeSet (T : Set (Sym2 V))
  letI : Fintype X.edgeSet := X.fintypeEdgeSet
  letI : Fintype B.edgeSet := B.fintypeEdgeSet
  let r := ⌈ρ*Fintype.card V⌉₊
  have hr : (r : ℝ)≤δ*Fintype.card V := by
    have hc := Nat.ceil_lt_add_one (mul_nonneg hρ.le (Nat.cast_nonneg (Fintype.card V)))
    change (r : ℝ) < ρ*Fintype.card V+1 at hc
    have hSmall := mul_le_mul_of_nonneg_right (show ρ≤δ/4 from min_le_right _ _) (Nat.cast_nonneg (Fintype.card V))
    linarith only [hc,hSmall,hδn]
  have hXd : ∀ v, X.degree v≤r := by
    have hd : ∀ v, degIn (BasalIncidence.cover D) v≤r := fun v => by
      exact_mod_cast (hDd v).le.trans (Nat.le_ceil _)
    intro v
    have hv := CorePaid.fromEdges_degree_le _ (CorePaid.edges_diagonal_free (CorePaid.basal_subset_edges ⟨D,hD⟩)) hd v
    convert hv using 1 <;> congr 2 <;> apply Subsingleton.elim
  have hBd : ∀ v, B.degree v≤dT := by
    intro v
    have hv := CorePaid.fromEdges_degree_le _ (CorePaid.edges_diagonal_free hT) hdT v
    convert hv using 1 <;> congr 2 <;> apply Subsingleton.elim
  have hXmem (e : Sym2 V) : e∈X.edgeSet ↔ e∈BasalIncidence.cover D := by
    simp only [X,SimpleGraph.edgeSet_fromEdgeSet,Set.mem_sdiff,mem_coe,Sym2.mem_diagSet]
    exact ⟨And.left,fun he => ⟨he,CorePaid.edges_diagonal_free (CorePaid.basal_subset_edges ⟨D,hD⟩) e he⟩⟩
  have hCover : ∀ e∈X.edgeFinset, ∃ Q, IsAllowed H F Q ∧ e∈triEdges Q := by
    intro e he
    have heD := (hXmem e).mp (by simpa only [SimpleGraph.mem_edgeFinset] using he)
    obtain ⟨Q,hQ,heQ⟩ := hD.exists_mem heD
    exact ⟨Q,hD.1 Q hQ,heQ⟩
  have hPacking : IsPacking H F D := ⟨hD.1,hD.2.1⟩
  have hStockCodeg : PairCodegreeBound (Rprev∪mapConfiguration ι D) (Lprev+1) :=
    hCodeg.union (pairCodegreeBound_mapConfiguration ι D 1 (pairCodegreeBound_of_linear (packing_linear hPacking)))
  obtain ⟨qSel,hqSel,hWithdrawal⟩ := fixed_core_positive_weighted_withdrawal
    ι H F a qRate κGeom ha hqRate hκGeom m hm hOdd W hOrder hWindow hWindowLower hPaths hPool
    X B r dT (CorePaid.fromEdges_le_host (CorePaid.basal_subset_edges ⟨D,hD⟩)) hCover hXd hBd τ hτ
    hnWithdrawal hr hTW (Rprev∪mapConfiguration ι D) (Lprev+1) hStockCodeg
  exact ⟨Praw,D,qSel,hStockH3,hStockLoad,hPsub,hPraw,hDP,hD,hAvoid,hDd,hSupply,hCount,hAmbient,hControls,hqSel,hWithdrawal⟩
end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.raw_stock_weighted_withdrawal_uniform_rich
