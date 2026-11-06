/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexOuterRawStartRich
public import RequestProject.TypedTriangle.VortexNativeOuterTests
public import RequestProject.TypedTriangle.VortexWindowRouteRate
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24 S07V25 S07V45
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open RawReference CorePaid ComponentRows

/-- A concrete outer start: no external-root or probability provider is an
input. The same W supports the original roots, the raw child profile, the
intrinsic quotient index and the subsequent inner vortex. -/
theorem native_outer_raw_start_rich {I : Type} (F : Set (Multiset I))
    (α C ε : ℝ) (h d T : ℕ) (K : IntrinsicPreparationKernel (α / 4) h ε d T)
    (hα : 0 < α) (hC : 0 < C) (hh : 1 ≤ h) :
    ∃ m : ℕ, ∃ a δ : ℝ, 0 < m ∧ 0 < a ∧ 0 < δ ∧ Odd (m+1) ∧ 3 ≤ m+1 ∧
      ∀ q : ℝ, 0 < q → q ≤ 1 / 32 → ∃ εRoute : ℝ, 0 < εRoute ∧
      ∀ β : ℕ → ℝ, (∀ j, 0 ≤ β j) →
        (∑ j ∈ range (d + (d+1)*Nat.log 2 T + 1), β j) ≤
          min δ (min ε (min (α / (4*(2:ℝ)^Nat.choose h 2)) (1/(8*max 1 (2*C))))) →
      ∀ N Mrequired : ℕ, 16 ≤ Mrequired → ∃ nRoot : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I), nRoot ≤ Fintype.card V →
        CommonNbrCond H F (8*α) → CleanHingeCond H F (8*α) h →
      ∀ μ : Finset V → ℝ, IsDiffuseSeed H F C μ →
      ∃ node : IntrinsicRawPreparedLayer H F α C β h N Mrequired d T μ,
        letI : DecidableEq (Survivors node.trim) := Classical.decEq _
        ∃ W : Finset (Survivors node.trim), Mrequired ≤ W.card ∧
          16*W.card ≤ Fintype.card (Survivors node.trim) ∧
          q*Fintype.card (Survivors node.trim)/2 ≤ W.card ∧
          (W.card:ℝ) < 2*q*Fintype.card (Survivors node.trim) ∧
          (1 - automaticRelativeError (Fintype.card (Survivors node.trim))) * q *
            Fintype.card (Survivors node.trim) ≤ (W.card:ℝ) ∧
          (W.card:ℝ) < (1 + automaticRelativeError (Fintype.card (Survivors node.trim))) * q *
            Fintype.card (Survivors node.trim) ∧
          CommonNbrCond (restrictedHost (restrictedHost H node.trim) (univ \ W)) F α ∧
          CleanHingeCond (restrictedHost (restrictedHost H node.trim) (univ \ W)) F α h ∧
          physicalPotential (restrictedHost (restrictedHost H node.trim) (univ \ W)) F T ≤
            d+(d+1)*Nat.log 2 T ∧
          node.index ≤ physicalPotential (restrictedHost (restrictedHost H node.trim) (univ \ W)) F T ∧
          RawProfileAt (restrictedHost (restrictedHost H node.trim) (univ \ W)) F C
            (globalRawProfileError 4 (max 1 (2*C)) β (Fintype.card (Survivors (univ \ W)))
              (physicalPotential (restrictedHost (restrictedHost H node.trim) (univ \ W)) F T))
            (survivorSampledWeights (restrictedWeights μ node.trim) W q) ∧
          (∀ u v, u ≠ v → ∀ k, ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
            (4*α)*Fintype.card V*q/2 ≤ ((commonNbrs H k u v) ∩ liftVertexSet node.trim W).card) ∧
          (∀ v x y, OrigAdm H.G H.lab F v x y →
            a*(Fintype.card V:ℝ)^m*q^m/4 ≤
              (pathsIn (link H.G H.lab F v) m x y (liftVertexSet node.trim W)).card) ∧
          S07V27.RouteProp H.G H.lab F (m+1) εRoute (liftVertexSet node.trim W) := by
  obtain ⟨m,a,δ,nNative,hm,ha,hδ,hOdd,hLen,hTests⟩ := native_outer_tests (8*α) h (by positivity)
  refine ⟨m,a,δ,hm,ha,hδ,hOdd,hLen,?_⟩
  intro q hq hq32
  have hq1 : q ≤ 1 := by linarith
  obtain ⟨θ,hθ,hTestsAt⟩ := hTests q hq hq1
  refine ⟨windowRouteRate a q m,windowRouteRate_pos m ha hq,?_⟩
  intro β hβ hBudget N Mrequired hM16
  have hBudgetRaw := hBudget.trans (min_le_right _ _)
  obtain ⟨nRaw,hRawStart⟩ := outer_raw_prepared_sample_with_tests_rich F α C ε h d T K hα hC hh
    β hβ hBudgetRaw N Mrequired q θ hq hq32 hθ
  refine ⟨max nRaw nNative,?_⟩
  intro V _ H hn h3 hClean μ hSeed
  obtain ⟨node,hNode3,hNodeClean,hPick⟩ := hRawStart H ((le_max_left _ _).trans hn) h3 hClean μ hSeed
  letI : DecidableEq (Survivors node.trim) := Classical.decEq _
  have hCut : (node.trim.card:ℝ) ≤ δ * Fintype.card V := by
    have hPrefix : (∑ j ∈ range node.index, β j) ≤
        ∑ j ∈ range (d+(d+1)*Nat.log 2 T+1), β j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by have h := node.index_le; omega))
        (by intro j _ _; exact hβ j)
    have hPrior : 0 ≤ ∑ j ∈ range (physicalPotential H F T), β j := sum_nonneg (by intro j _; exact hβ j)
    have hs := mul_le_mul_of_nonneg_left (hPrefix.trans (hBudget.trans (min_le_left _ _)))
      (by positivity : (0:ℝ) ≤ Fintype.card V)
    have hp := mul_nonneg (by positivity : (0:ℝ) ≤ Fintype.card V) hPrior
    nlinarith [node.cost]
  obtain ⟨E,hJ,hTails,hGood⟩ := hTestsAt H F ((le_max_right _ _).trans hn) h3 hClean.hingeCond
    node.trim hCut (hM16.trans node.lower)
  obtain ⟨W,hWmin,hShrink,hLow,hUp,hRelLow,hRelUp,h3Child,hCleanChild,hIndex,hNext,hRawChild,hAvoid⟩ :=
    hPick (J := ((V×V×V) ⊕ (V×V×V))) hJ E hTails
  obtain ⟨hPools,hPaths⟩ := hGood W hAvoid
  have hHASize : (Fintype.card (Survivors node.trim):ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_le_of_injective
      (fun v : Survivors node.trim => v.1) (fun _ _ h => Subtype.ext h)
  have hWindow : ((liftVertexSet node.trim W).card:ℝ) ≤ 2*q*Fintype.card V := by
    rw [card_liftVertexSet]
    exact hUp.le.trans (mul_le_mul_of_nonneg_left hHASize (by positivity))
  have hW16 : (16:ℝ) ≤ (liftVertexSet node.trim W).card := by
    rw [card_liftVertexSet]
    exact_mod_cast hM16.trans hWmin
  have hOrder : 2 ≤ q*(Fintype.card V:ℝ) := by nlinarith
  have hPaths' : ∀ v x y, OrigAdm H.G H.lab F v x y →
      a*(Fintype.card V:ℝ)^m*q^m/4 ≤
        (pathsIn (link H.G H.lab F v) m x y (liftVertexSet node.trim W)).card := by
    intro v x y hv
    convert hPaths v x y hv using 1 <;> ring
  have hRoute := routeProp_of_window_path_count H.G H.lab F (liftVertexSet node.trim W)
    a q m ha hq hm hOrder hWindow hPaths'
  refine ⟨node,W,hWmin,hShrink,hLow,hUp,hRelLow,hRelUp,h3Child,hCleanChild,hIndex,hNext,hRawChild,?_,hPaths',hRoute⟩
  intro u v huv k hk
  convert hPools u v huv k hk using 1 <;> ring

#print axioms native_outer_raw_start_rich
end TypedTriangle.Vortex

