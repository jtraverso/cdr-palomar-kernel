/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexNativeOuterStartRich
public import RequestProject.TypedTriangle.VortexRelativeRawPathsPreparedVortex
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24 S07V25 S07V45
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open RawReference CorePaid ComponentRows

/-- A concrete outer sample followed by the constructed inner vortex. The
terminal bound is fixed before the outer rate and the outer prepared order.
The same preparation kernel, quotient counter and literal raw weights are
used on both sides of the outer sample. -/
theorem exists_outer_inner_raw_prepared_vortex {I : Type} (F : Set (Multiset I))
    (α C : ℝ) (h : ℕ) (hα : 0 < α) (hh : 1 ≤ h) (hC : 0 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ d T mInner : ℕ, ∃ aInner : ℝ,
    ∃ mOuter : ℕ, ∃ aOuter δOuter : ℝ,
      1 ≤ T ∧ IntrinsicPreparationKernel (α / 4) h ε d T ∧
      0 < mInner ∧ 0 < aInner ∧ Odd (mInner+1) ∧ 3 ≤ mInner+1 ∧
      0 < mOuter ∧ 0 < aOuter ∧ 0 < δOuter ∧ Odd (mOuter+1) ∧ 3 ≤ mOuter+1 ∧
      ∀ qInner : ℝ, 0 < qInner → qInner ≤ 1/32 →
      ∃ εRouteInner : ℝ, 0 < εRouteInner ∧
      ∀ β : ℕ → ℝ, (∀ j, 0 ≤ β j) →
        (∑ j ∈ range (d+(d+1)*Nat.log 2 T+1), β j) ≤
          min δOuter (min ε (min (α/(4*(2:ℝ)^Nat.choose h 2)) (1/(8*max 1 (2*C))))) →
      ∀ Ninner Mrequired : ℕ,
      ∃ M nInner : ℕ, Mrequired ≤ M ∧ 1 ≤ M ∧ ∃ t : ℝ, 0 < t ∧
      ∀ qOuter : ℝ, 0 < qOuter → qOuter ≤ 1/32 →
      ∃ εRouteOuter : ℝ, 0 < εRouteOuter ∧
      ∀ Nouter : ℕ, ∃ nRoot : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I), nRoot ≤ Fintype.card V →
        CommonNbrCond H F (8*α) → CleanHingeCond H F (8*α) h →
      ∀ μ : Finset V → ℝ, IsDiffuseSeed H F C μ →
      ∃ node : IntrinsicRawPreparedLayer H F α C β h Nouter (max 16 nInner) d T μ,
        letI : DecidableEq (Survivors node.trim) := Classical.decEq _
        ∃ W : Finset (Survivors node.trim), max 16 nInner ≤ W.card ∧
          16*W.card ≤ Fintype.card (Survivors node.trim) ∧
          qOuter*Fintype.card (Survivors node.trim)/2 ≤ W.card ∧
          (W.card:ℝ) < 2*qOuter*Fintype.card (Survivors node.trim) ∧
          (1-automaticRelativeError (Fintype.card (Survivors node.trim)))*qOuter*
            Fintype.card (Survivors node.trim) ≤ (W.card:ℝ) ∧
          (W.card:ℝ) < (1+automaticRelativeError (Fintype.card (Survivors node.trim)))*qOuter*
            Fintype.card (Survivors node.trim) ∧
          node.index ≤ physicalPotential (restrictedHost (restrictedHost H node.trim) (univ \ W)) F T ∧
          (∀ u v, u ≠ v → ∀ k, ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
            (4*α)*Fintype.card V*qOuter/2 ≤ ((commonNbrs H k u v) ∩ liftVertexSet node.trim W).card) ∧
          (∀ v x y, OrigAdm H.G H.lab F v x y →
            aOuter*(Fintype.card V:ℝ)^mOuter*qOuter^mOuter/4 ≤
              (pathsIn (link H.G H.lab F v) mOuter x y (liftVertexSet node.trim W)).card) ∧
          S07V27.RouteProp H.G H.lab F (mOuter+1) εRouteOuter (liftVertexSet node.trim W) ∧
          ∃ chain : IntrinsicRawPathsPreparedVortex F α qInner C β h Ninner M d T mInner aInner
              εRouteInner t (restrictedHost (restrictedHost H node.trim) (univ \ W))
              (survivorSampledWeights (restrictedWeights μ node.trim) W qOuter),
            chain.HasRelativeWindows := by
  obtain ⟨ε,hε,d,T,mInner,aInner,hT,K,hmInner,haInner,hOddInner,hLenInner,hInnerByQ⟩ :=
    exists_intrinsic_raw_paths_prepared_vortex_with_relative_windows F α C h hα hh hC
  obtain ⟨mOuter,aOuter,δOuter,hmOuter,haOuter,hδOuter,hOddOuter,hLenOuter,hOuterByQ⟩ :=
    native_outer_raw_start_rich F α C ε h d T K hα hC hh
  refine ⟨ε,hε,d,T,mInner,aInner,mOuter,aOuter,δOuter,hT,K,hmInner,haInner,hOddInner,hLenInner,
    hmOuter,haOuter,hδOuter,hOddOuter,hLenOuter,?_⟩
  intro qInner hqInner hqInner32
  obtain ⟨εRouteInner,hRouteInner,hInnerByBeta⟩ := hInnerByQ qInner hqInner hqInner32
  refine ⟨εRouteInner,hRouteInner,?_⟩
  intro β hβ hBudget Ninner Mrequired
  have hBudgetInner := hBudget.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨M,nInner,hMrequired,hM,t,ht,hInnerBuild⟩ :=
    hInnerByBeta β hβ hBudgetInner Ninner Mrequired
  refine ⟨M,nInner,hMrequired,hM,t,ht,?_⟩
  intro qOuter hqOuter hqOuter32
  obtain ⟨εRouteOuter,hRouteOuter,hOuterByBeta⟩ := hOuterByQ qOuter hqOuter hqOuter32
  refine ⟨εRouteOuter,hRouteOuter,?_⟩
  intro Nouter
  obtain ⟨nRoot,hOuterBuild⟩ := hOuterByBeta β hβ hBudget Nouter (max 16 nInner) (le_max_left _ _)
  refine ⟨nRoot,?_⟩
  intro V _ H hn h3 hClean μ hSeed
  obtain ⟨node,W,hWmin,hShrink,hLow,hUp,hRelLow,hRelUp,h3Child,hCleanChild,hChildIndex,
    hNext,hRawChild,hPools,hPaths,hRoute⟩ := hOuterBuild H hn h3 hClean μ hSeed
  letI : DecidableEq (Survivors node.trim) := Classical.decEq _
  have hnChild : nInner ≤ Fintype.card (Survivors (univ \ W)) := by
    rw [CorePaid.card_survivors_compl W]
    exact (le_max_right _ _).trans hWmin
  obtain ⟨chain,hMetadata⟩ := hInnerBuild
    (restrictedHost (restrictedHost H node.trim) (univ \ W)) hnChild h3Child hCleanChild
    (survivorSampledWeights (restrictedWeights μ node.trim) W qOuter) hRawChild
  exact ⟨node,W,hWmin,hShrink,hLow,hUp,hRelLow,hRelUp,hNext,hPools,hPaths,hRoute,chain,hMetadata⟩

#print axioms exists_outer_inner_raw_prepared_vortex
end TypedTriangle.Vortex
