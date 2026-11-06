module
public import RequestProject.TypedTriangle.PaschConcreteLayerCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open ProtectedNibble LocalizedCover

/-- The same explicit reserve budget works before the monitor scale and
family exponents are chosen. The residual seed and all controls still use
one literal packing; only the later order depends on those choices. -/
theorem protected_joint_packing_uniform_reserve {I : Type} (F : Set (Multiset I))
    (C α τStat σ εAmbient : ℝ) (h : ℕ) (hC : 1 ≤ C) (hα : 0 < α)
    (hτStat : 0 < τStat) (hσ : 0 < σ) (hεAmbient : 0 < εAmbient) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ L : ℝ, 0 < L → ∀ q bankL : ℕ,
      ∀ η τ : ℝ, 0 < η → 0 < τ → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (R : Finset (Sym2 V)) (D : Finset (Finset V)) (d : ℕ),
      n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
      CommonNbrCond H F α → HingeCond H F α h → IsDecomposition H F R D →
      (∀ v, degIn R v ≤ d) → (d:ℝ) ≤ ε*Fintype.card V →
      ∀ (κ ι ν : Type) [Fintype κ] [Fintype ι] [Fintype ν]
        (bad : κ → Finset V) (loc : κ → Sym2 V → ℝ) (full : ι → Sym2 V → ℝ)
        (w : ν → Finset V → ℝ),
        ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^q →
        (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*L*(T∩bad k).card) →
        (∀ k T, IsAllowed H F T → |triSum (full k) T| ≤ 3*L*T.card) →
        (∀ k T, IsAllowed H F T → |w k T| ≤ 1) →
        ∀ B : Finset (Finset V), PairCodegreeBound B bankL → (∀ T ∈ B, T.card = 3) →
        ∀ (X : Type) [Fintype X] (e : V ↪ X) (Rprev : Finset (Finset X)) (Lprev : ℕ),
        PairCodegreeBound Rprev Lprev →
        ∃ ψ : Finset V → ℝ, IsDiffuseSeed (residual H R) F (2*C) ψ ∧
          (∀ T, ψ T ≠ 0 → IsAllowed (residual H R) F T) ∧
          (∀ T, IsAllowed (residual H R) F T →
            |ψ T-φ T| ≤ ExplicitSeed.seedPointwiseCost α C h*d/(Fintype.card V:ℝ)^2) ∧
        ∀ (ω : Type) [Fintype ω] (Yextra : ℕ → ω → Finset (Finset V) → ℝ),
        Fintype.card ω ≤ (Fintype.card V)^q →
        (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ Yextra ℓ k S) →
        ∃ P : Finset (Finset V), IsPacking H F P ∧ Disjoint (P.biUnion triEdges) R ∧
          IsPhysical H F ((edges H\R)\P.biUnion triEdges) ∧
          (∀ v, (((((edges H\R)\P.biUnion triEdges).filter (fun e => v ∈ e)).card):ℝ) ≤ η*Fintype.card V) ∧
          (∀ k, |edgeSum (loc k) ((edges H\R)\P.biUnion triEdges)| ≤ τ*Fintype.card V*(bad k).card) ∧
          (∀ k, |edgeSum (full k) ((edges H\R)\P.biUnion triEdges)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
          (∀ k, |(∑ T ∈ P, w k T)-(∑ T ∈ allowed H F, φ T*w k T)| ≤ (τ+τStat/2)*(Fintype.card V:ℝ)^2) ∧
          |(count P:ℝ)-target φ (allowed H F)| ≤ σ*(Fintype.card V:ℝ)^2 ∧
          (|(∑ T ∈ P, childPaddedWeight e Rprev Lprev T)-
             (∑ T ∈ allowed (residual H R) F, ψ T*childPaddedWeight e Rprev Lprev T)| ≤
            εAmbient*(∑ T ∈ allowed (residual H R) F, ψ T*childPaddedWeight e Rprev Lprev T)) ∧
          (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 →
            let A := allowed (residual H R) F
            let n := (Fintype.card V:ℝ)
            let θ := floorWeights A ψ n
            |PatternStatistics.statistic (completionWeight B) ℓ P-mixedMass A B θ ℓ| ≤
              (n^2)^(-egj13Epsilon)*(2*(Nat.choose 4 ℓ:ℝ)*target θ A+mixedMass A B θ ℓ)) ∧
          ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k : ω,
            floorTupleTestControl (allowed (residual H R) F) ψ P (Yextra ℓ k) ℓ := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let K := ExplicitSeed.seedPointwiseCost α C h
  have hK : 0 ≤ K := ExplicitSeed.seedPointwiseCost_nonneg h hα hC0
  let δ := targetPaymentBudget C K σ
  have hδ : 0 < δ := targetPaymentBudget_pos hC0 hK hσ
  have hδbounds := targetPaymentBudget_bounds hC0 hK hσ
  let εS := ExplicitSeed.seedExactBudget C α h
  have hεS : 0 < εS := by
    change 0 < RawReference.Explicit.seedBudget (1/C) C α h
    exact RawReference.Explicit.seedBudget_pos h (by positivity)
      (by rw [div_le_iff₀ hC0]; nlinarith only [hC]) hα
  let ε := min εS (min (α/4) (min δ (τStat/(2*(K+1)))))
  have hε : 0 < ε := lt_min hεS (lt_min (by positivity) (lt_min hδ (by positivity)))
  have hεSeed : ε ≤ εS := min_le_left _ _
  have hεGeometry : ε ≤ α/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hεPasch : ε ≤ δ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεMoment : (K+1)*ε ≤ τStat/2 := by
    have hh : ε ≤ τStat/(2*(K+1)) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*(K+1))).mp hh
    nlinarith only [hh']
  refine ⟨ε,hε,?_⟩
  intro L hL q bankL η τ hη hτ
  obtain ⟨NP,hPack⟩ := joint_packing_with_triangle_monitors_pasch_bank_ambient_and_tuple_tests
    (2*C) (α/2) η τ L (σ/2) εAmbient q bankL (by linarith only [hC]) (by positivity)
      hη hτ hL (by positivity) hεAmbient
  refine ⟨max (ExplicitSeed.seedExactOrder C) (max NP 1),?_⟩
  intro V _ H φ R D d hn hφ h2 h3 h4 hD hdeg hd κ ι ν _ _ _ bad loc full w hcount hloc hfull hw B hBankL hBank X _ e Rprev Lprev hPrev
  have hnNat : 0 < Fintype.card V := by omega
  have hn0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast hnNat
  have hRsub : R ⊆ edges H := by
    rw [←hD.2.2]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hD.1 T hT) heT
  have hdS : (d:ℝ) ≤ εS*Fintype.card V := hd.trans (mul_le_mul_of_nonneg_right hεSeed hn0.le)
  have hd3 : (d:ℝ) ≤ α/4*Fintype.card V := hd.trans (mul_le_mul_of_nonneg_right hεGeometry hn0.le)
  have hdδ : (d:ℝ) ≤ δ*Fintype.card V := hd.trans (mul_le_mul_of_nonneg_right hεPasch hn0.le)
  obtain ⟨ψ,hψ,hSupp,hClose⟩ := ExplicitSeed.seed_persistence_exact_with_pointwise_bound_explicit
    (F:=F) hC hα h H φ R D d ((le_max_left _ _).trans hn) hφ h4 hRsub hD hdeg hdS
  have hres3 := residual_commonNbrCond h3 R d hdeg hd3
  refine ⟨ψ,hψ,hSupp,hClose,?_⟩
  intro ω _ Yextra hω hExtra
  obtain ⟨P,hPsub,hP,hSparse,hLocal,hGlobal,hTriangles,hPasch,hAmbient,hMixed,hControls⟩ :=
    hPack (residual H R) F ψ ((le_max_left _ _).trans ((le_max_right _ _).trans hn)) hψ hres3 X e Rprev Lprev hPrev
      κ ι ν bad loc full w hcount
      (fun k T hT => hloc k T (isAllowed_mono (subHost_le H _) rfl hT))
      (fun k T hT => hfull k T (isAllowed_mono (subHost_le H _) rfl hT))
      (fun k T hT => hw k T (isAllowed_mono (subHost_le H _) rfl hT)) B hBankL hBank
        ω Yextra hω hExtra
  have hPH : IsPacking H F P := ⟨fun T hT =>
    isAllowed_mono (subHost_le H _) rfl (hP.1 T hT),hP.2⟩
  have hJ : edges (residual H R) = edges H\R := Residual.edges_subHost_eq sdiff_subset
  have hPE : P.biUnion triEdges ⊆ edges H\R := by
    rw [←hJ]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  have hDis : Disjoint (P.biUnion triEdges) R :=
    disjoint_left.mpr fun e he hR => (mem_sdiff.mp (hPE he)).2 hR
  have hPhys := isPhysical_sdiff (isPhysical_sdiff_of_decomposition h2 hD hRsub)
    (isPhysical_of_isDecomposition hPH.isDecomposition) hPE
  have hTransfer := protected_target_transfer hC0 hφ R hRsub K δ (d:ℝ) hK hδ.le hdδ
    hδbounds.1 (fun v => (show (degIn R v:ℝ) ≤ d by exact_mod_cast hdeg v).trans hdδ) hClose hn0
  have hPaid : |target ψ (allowed (residual H R) F)-target φ (allowed H F)| ≤
      (σ/2)*(Fintype.card V:ℝ)^2 := hTransfer.trans
    (mul_le_mul_of_nonneg_right hδbounds.2 (sq_nonneg _))
  have hClose' : ∀ T, IsAllowed (residual H R) F T → |ψ T-φ T| ≤ (K*ε)/Fintype.card V := by
    intro T hT
    calc
      _ ≤ K*d/(Fintype.card V:ℝ)^2 := hClose T hT
      _ ≤ K*(ε*Fintype.card V)/(Fintype.card V:ℝ)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hK) (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt hn0] <;> ring
  have hDegreeε (v : V) : (degIn R v:ℝ) ≤ ε*Fintype.card V :=
    (show (degIn R v:ℝ) ≤ d by exact_mod_cast hdeg v).trans hd
  have hRcard := TriangleMonitors.edge_card_le_of_degree_bound R ε hDegreeε
  refine ⟨P,hPH,hDis,hPhys,?_,?_,?_,?_,?_,hAmbient,hMixed,hControls⟩
  · simpa only [hJ] using hSparse
  · intro k
    simpa only [hJ] using hLocal k
  · intro k
    simpa only [hJ] using hGlobal k
  · intro k
    have hb := TriangleMonitors.triangle_seed_statistic_comparison hC0 hφ R hRsub (K*ε)
      (mul_nonneg hK hε.le) hnNat hClose' (w k) (hw k)
    have hb' : |(∑ T ∈ allowed (residual H R) F, ψ T*w k T)-
        (∑ T ∈ allowed H F, φ T*w k T)| ≤ (τStat/2)*(Fintype.card V:ℝ)^2 := by
      calc
        _ ≤ (K*ε)*(Fintype.card V:ℝ)^2+R.card := hb
        _ ≤ (K*ε)*(Fintype.card V:ℝ)^2+ε*(Fintype.card V:ℝ)^2 := add_le_add (le_refl _) hRcard
        _ = ((K+1)*ε)*(Fintype.card V:ℝ)^2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hεMoment (sq_nonneg _)
    calc
      _ ≤ |(∑ T ∈ P, w k T)-(∑ T ∈ allowed (residual H R) F, ψ T*w k T)|+
          |(∑ T ∈ allowed (residual H R) F, ψ T*w k T)-(∑ T ∈ allowed H F, φ T*w k T)| := abs_sub_le _ _ _
      _ ≤ τ*(Fintype.card V:ℝ)^2+(τStat/2)*(Fintype.card V:ℝ)^2 := add_le_add (hTriangles k) hb'
      _ = _ := by ring
  · calc
      _ ≤ |(count P:ℝ)-target ψ (allowed (residual H R) F)|+
          |target ψ (allowed (residual H R) F)-target φ (allowed H F)| := abs_sub_le _ _ _
      _ ≤ (σ/2)*(Fintype.card V:ℝ)^2+(σ/2)*(Fintype.card V:ℝ)^2 := add_le_add hPasch hPaid
      _ = _ := by ring


#print axioms protected_joint_packing_uniform_reserve
end TypedTriangle.Pasch
