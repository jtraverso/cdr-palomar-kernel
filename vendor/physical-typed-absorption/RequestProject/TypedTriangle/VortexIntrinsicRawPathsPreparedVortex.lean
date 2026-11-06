/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexIntrinsicRawPreparedVortex
public import RequestProject.TypedTriangle.VortexGlobalCleanRawPathsStep
public import RequestProject.TypedTriangle.VortexIntrinsicPreparationKernel
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A finite, globally prepared geometric vortex. All hosts and samples are
actual induced subtypes. This constructs no paid layers or decomposition. -/
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open S07V24 S07V25 ComponentRows
open RawReference

inductive IntrinsicRawPathsPreparedVortex {I : Type} (F : Set (Multiset I))
    (α₀ q C : ℝ) (β : ℕ → ℝ) (h N M d T m : ℕ) (a εRoute t : ℝ) :
    ∀ {V : Type} [Fintype V], Host V I → (Finset V → ℝ) → Type 1 where
  | terminal {V : Type} [Fintype V] {H : Host V I} {μ : Finset V → ℝ}
      (node : IntrinsicRawPreparedLayer H F α₀ C β h N M d T μ)
      (upper : (Fintype.card (Survivors node.trim) : ℝ) ≤ t) :
      IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ
  | descend {V : Type} [Fintype V] {H : Host V I} {μ : Finset V → ℝ}
      (node : IntrinsicRawPreparedLayer H F α₀ C β h N M d T μ)
      (W : Finset (Survivors node.trim))
      (lower : 2 * M ≤ W.card)
      (shrink : 16 * W.card ≤ Fintype.card (Survivors node.trim))
      (route : letI : DecidableEq (Survivors node.trim) := Classical.decEq _
        S07V27.RouteProp (restrictedHost H node.trim).G (restrictedHost H node.trim).lab F (m + 1) εRoute W)
      (paths : letI : DecidableEq (Survivors node.trim) := Classical.decEq _
        ∀ v x y, AdmPair (activeComps (restrictedHost H node.trim).G (restrictedHost H node.trim).lab F)
          (fun v B => IsBip (restrictedHost H node.trim).G (restrictedHost H node.trim).lab F (v,B))
          (colG (restrictedHost H node.trim).G (restrictedHost H node.trim).lab F) v x y →
          a * (Fintype.card (Survivors node.trim) : ℝ)^m * q^m / 2 ≤
            (pathsIn (link (restrictedHost H node.trim).G (restrictedHost H node.trim).lab F v) m x y W).card)
      (intermediate : letI : DecidableEq (Survivors node.trim) := Classical.decEq _
        ∀ U : Finset (Survivors node.trim), W ⊆ U →
        CommonNbrCond (restrictedHost (restrictedHost H node.trim) (univ \ U)) F (α₀ * q ^ h / 4) ∧
        HingeCond (restrictedHost (restrictedHost H node.trim) (univ \ U)) F (α₀ * q ^ h / 4) h)
      (next_index : letI : DecidableEq (Survivors node.trim) := Classical.decEq _
        node.index ≤ physicalPotential
        (restrictedHost (restrictedHost H node.trim) (univ \ W)) F T)
      (tail : letI : DecidableEq (Survivors node.trim) := Classical.decEq _
        IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t
        (restrictedHost (restrictedHost H node.trim) (univ \ W))
        (survivorSampledWeights (restrictedWeights μ node.trim) W q)) :
      IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ

def IntrinsicRawPathsPreparedVortex.terminalOrder {I V : Type} [Fintype V]
    {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ} {h N M d T m : ℕ} {a εRoute t : ℝ} {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) : ℕ := by
  induction chain with
  | terminal node upper => exact Fintype.card (Survivors node.trim)
  | descend node W lower shrink route paths intermediate next_index tail ih => exact ih

theorem IntrinsicRawPathsPreparedVortex.terminalOrder_bounds {I V : Type} [Fintype V]
    {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ} {h N M d T m : ℕ} {a εRoute t : ℝ} {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) :
    M ≤ chain.terminalOrder ∧ (chain.terminalOrder : ℝ) ≤ t := by
  induction chain with
  | terminal node upper => exact ⟨node.lower, upper⟩
  | descend node W lower shrink route paths intermediate next_index tail ih => exact ih

def IntrinsicRawPathsPreparedVortex.forgetPaths {I V : Type} [Fintype V]
    {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ} {h N M d T m : ℕ}
    {a εRoute t : ℝ} {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) :
    IntrinsicRawPreparedVortex F α₀ q C β h N M d T (m + 1) εRoute t H μ := by
  induction chain with
  | terminal node upper => exact .terminal node upper
  | descend node W lower shrink route paths intermediate next_index tail ih =>
    exact .descend node W lower shrink route intermediate next_index ih

theorem IntrinsicRawPathsPreparedVortex.terminalOrder_forgetPaths {I V : Type} [Fintype V]
    {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ} {h N M d T m : ℕ}
    {a εRoute t : ℝ} {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) :
    chain.forgetPaths.terminalOrder = chain.terminalOrder := by
  induction chain with
  | terminal node upper => rfl
  | descend node W lower shrink route paths intermediate next_index tail ih => exact ih

theorem exists_intrinsic_raw_paths_prepared_vortex {I : Type} (F : Set (Multiset I))
    (α₀ C : ℝ) (h : ℕ) (hα : 0 < α₀) (hh : 1 ≤ h) (hC : 0 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ d T m : ℕ, ∃ a : ℝ,
      1 ≤ T ∧ IntrinsicPreparationKernel (α₀ / 4) h ε d T ∧ 0 < m ∧ 0 < a ∧ Odd (m + 1) ∧ 3 ≤ m + 1 ∧
      ∀ q : ℝ, 0 < q → q ≤ 1 / 32 → ∃ εRoute : ℝ, 0 < εRoute ∧
      let L := d + (d + 1) * Nat.log 2 T
      ∀ β : ℕ → ℝ, (∀ j, 0 ≤ β j) → (∑ j ∈ range (L + 1), β j) ≤ ε →
      ∀ N Mrequired : ℕ, ∃ M nRoot : ℕ, Mrequired ≤ M ∧ 1 ≤ M ∧ ∃ t : ℝ, 0 < t ∧
      ∀ {V : Type} [Fintype V] (H : Host V I), nRoot ≤ Fintype.card V →
        CommonNbrCond H F α₀ → CleanHingeCond H F α₀ h →
        ∀ μ : Finset V → ℝ,
          RawProfileAt H F C (globalRawProfileError 4 (max 1 (2 * C)) β (Fintype.card V)
            (physicalPotential H F T)) μ → Nonempty (IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) := by
  let D : ℝ := 2 ^ Nat.choose h 2
  have hD : 0 < D := by positivity
  obtain ⟨εPrep, hεPrep, d, T, hT, hPrepareAll⟩ :=
    intrinsic_preparation_with_clean_geometry (α₀ / 4) h (by positivity)
  let E : ℝ := max 1 (2 * C)
  have hE1 : 1 ≤ E := le_max_left _ _
  have hEC : 2 * C ≤ E := le_max_right _ _
  have hE : 0 < E := by linarith
  obtain ⟨m, a, hm, ha, hOdd, hLen, hStepsByQ⟩ :=
    exists_global_clean_raw_paths_step α₀ C D h hα hh hC hD.le
  let ε := min εPrep (min (α₀ / (4 * D)) (1 / (8 * E)))
  have hε : 0 < ε := lt_min hεPrep (lt_min (by positivity) (by positivity))
  have hKernelBig : IntrinsicPreparationKernel (α₀ / 4) h εPrep d T := hPrepareAll
  have hKernel := hKernelBig.mono (show ε ≤ εPrep from min_le_left _ _)
  refine ⟨ε, hε, d, T, m, a, hT, hKernel, hm, ha, hOdd, hLen, ?_⟩
  intro q hq hq32
  obtain ⟨εRoute, hRoutePos, hStepAll⟩ := hStepsByQ q hq hq32
  refine ⟨εRoute, hRoutePos, ?_⟩
  dsimp only
  let L := d + (d + 1) * Nat.log 2 T
  intro β hβ hBudget N Mrequired
  obtain ⟨nPrep, hQuot, hPrepare⟩ := hPrepareAll N
  let κ : ℝ := α₀ * q ^ h / 4
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let R : ℝ := max ((8 * ((h : ℝ) + 1)) ^ 4)
    (max ((32 : ℝ)^4) (max (4 / κ) (2 * (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 / κ)))
  let M := max (max nPrep Mrequired) (max 1 (⌈R⌉₊ + 1))
  have hMprep : nPrep ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMreq : Mrequired ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hM1 : 1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hCeil : (⌈R⌉₊ : ℝ) ≤ M := by
    exact_mod_cast (show ⌈R⌉₊ ≤ M from (Nat.le_succ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hRM : R ≤ M := (Nat.le_ceil _).trans hCeil
  have hPower : (8 * ((h : ℝ) + 1)) ^ 4 ≤ M := (le_max_left _ _).trans hRM
  have hW1 : 3 < κ * M := by
    have hs : 4 / κ ≤ (M : ℝ) := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hRM
    have hs' := (div_le_iff₀ hκ).mp hs
    linarith
  have hW2 : (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 ≤ κ / 2 * M := by
    have hs : 2 * (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 / κ ≤ (M : ℝ) :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hRM
    have hs' := (div_le_iff₀ hκ).mp hs
    nlinarith
  have hBudgetPrep := hBudget.trans (min_le_left _ _)
  have hDebt : D * (∑ j ∈ range (L + 1), β j) ≤ α₀ / 4 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 4 * D)).mp (hBudget.trans ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith
  have hFloor (n : ℝ) (r : ℕ) (hn : (M : ℝ) ≤ n) (hr : r ≤ L) :
      α₀ / 2 ≤ globalGeometryFloor α₀ h D β n r := by
    have hp : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range (L + 1), β j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intro j _ _; exact hβ j)
    exact globalGeometryFloor_half_le α₀ D h β n r hα.le (hPower.trans hn)
      ((mul_le_mul_of_nonneg_left hp hD.le).trans hDebt)
  have hRawDebt : E * (∑ j ∈ range (L + 1), β j) ≤ 1 / 8 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 8 * E)).mp
      (hBudget.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith
  have hRawPower : (32 : ℝ)^4 ≤ M :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hRM
  have hRawCap (n : ℝ) (r : ℕ) (hn : (M : ℝ) ≤ n) (hr : r ≤ L) :
      globalRawProfileError 4 E β n r ≤ 1 / 4 := by
    have he := automaticRelativeError_le_of_power_bound 32 n (by norm_num) (hRawPower.trans hn)
    norm_num at he
    have hp : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range (L + 1), β j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intro j _ _; exact hβ j)
    apply globalRawProfileError_le_cap 4 E (1 / 4) β n r
    · linarith
    · norm_num
      exact (mul_le_mul_of_nonneg_left hp hE.le).trans hRawDebt
  obtain ⟨Ns, hNs, hStep⟩ := hStepAll (2 * M) L β (by omega) hβ hDebt
  let t : ℝ := max Ns M
  have ht : 0 < t := hNs.trans_le (le_max_left _ _)
  refine ⟨M, 2 * M, hMreq, hM1, t, ht, ?_⟩
  have hAll : ∀ n : ℕ, ∀ {V : Type} [Fintype V] (H : Host V I), Fintype.card V = n →
      2 * M ≤ n → physicalPotential H F T ≤ L →
      CommonNbrCond H F (globalGeometryFloor α₀ h D β n (physicalPotential H F T)) →
      CleanHingeCond H F (globalGeometryFloor α₀ h D β n (physicalPotential H F T)) h →
      ∀ μ : Finset V → ℝ, RawProfileAt H F C (globalRawProfileError 4 E β n (physicalPotential H F T)) μ →
      Nonempty (IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ H hcard hMin hp h3 hClean μ hRaw
      have hMcur : M ≤ Fintype.card V := by omega
      have hMcurR : (M : ℝ) ≤ Fintype.card V := by exact_mod_cast hMcur
      have hFloorCur := hFloor (Fintype.card V) (physicalPotential H F T) hMcurR hp
      rw [← hcard] at h3 hClean hRaw
      obtain ⟨r, hr, A, hpEnter, hpA, hCost, hHalf, h3A, hCleanA, hPc⟩ :=
        hPrepare β hβ hBudgetPrep H F _ (hMprep.trans hMcur) (by linarith) h3 hClean
      letI : DecidableEq (Survivors A) := Classical.decEq _
      have hMA : M ≤ Fintype.card (Survivors A) := by
        have hnR : (2 : ℝ) * M ≤ Fintype.card V := by exact_mod_cast (show 2 * M ≤ Fintype.card V by omega)
        have hOut : (M : ℝ) ≤ Fintype.card (Survivors A) := by linarith
        exact_mod_cast hOut
      have hMAR : (M : ℝ) ≤ Fintype.card (Survivors A) := by exact_mod_cast hMA
      have hSize : Fintype.card (Survivors A) ≤ Fintype.card V := by
        have hc := card_survivors_add_card A
        omega
      have hSizeR : (Fintype.card (Survivors A) : ℝ) ≤ Fintype.card V := by exact_mod_cast hSize
      have hAPos : (0 : ℝ) < Fintype.card (Survivors A) := by
        exact_mod_cast (show 0 < Fintype.card (Survivors A) by omega)
      have hTrim := globalGeometryFloor_trim α₀ D h β hα.le (Fintype.card V)
        (Fintype.card (Survivors A)) (physicalPotential H F T) r hAPos hSizeR
      have h3Prepared := commonNbrCond_mono h3A hTrim
      have hCleanPrepared := hCleanA.mono hTrim
      have hPreparedFloor := hFloor (Fintype.card (Survivors A)) r hMAR hr
      have h3base := commonNbrCond_mono h3Prepared (show α₀ / 4 ≤ _ by linarith)
      have hCleanbase := hCleanPrepared.mono (show α₀ / 4 ≤ _ by linarith)
      have hRawCapCur := hRawCap (Fintype.card V) (physicalPotential H F T) hMcurR hp
      have hnPos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
      let debt := (∑ j ∈ range r, β j) - ∑ j ∈ range (physicalPotential H F T), β j
      have hDebt0 : 0 ≤ debt := by
        have hs := sum_le_sum_of_subset_of_nonneg (range_mono hpEnter) (by intro j _ _; exact hβ j)
        dsimp [debt]
        linarith
      have hDebtCap : debt ≤ ε := by
        have hs : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range (L + 1), β j :=
          sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intro j _ _; exact hβ j)
        have hp0 : 0 ≤ ∑ j ∈ range (physicalPotential H F T), β j := sum_nonneg (by intro j _; exact hβ j)
        dsimp [debt]
        linarith
      have hDebt1 : debt < 1 := by
        have hεcap : ε ≤ 1 / (8 * E) := (min_le_right _ _).trans (min_le_right _ _)
        have hs := (le_div_iff₀ (by positivity : 0 < 8 * E)).mp (hDebtCap.trans hεcap)
        nlinarith
      have hRawPrepared := raw_profile_restrict_global H F C E β μ (physicalPotential H F T) r A debt
        hC hE1 hEC hβ hnPos hRaw (by linarith) hDebt0 hDebt1
        (by dsimp [debt]; nlinarith [hCost]) le_rfl
      have hRawCapPrepared := hRawCap (Fintype.card (Survivors A)) r hMAR hr
      let baseNode : IntrinsicPreparedLayer H F α₀ β h N M d T :=
        ⟨A, r, hr, hpEnter, hpA, hCost, h3base, hCleanbase, hPc, hMA⟩
      let node : IntrinsicRawPreparedLayer H F α₀ C β h N M d T μ :=
        ⟨baseNode, hRawPrepared, hRawCapPrepared⟩
      by_cases hStop : (Fintype.card (Survivors A) : ℝ) ≤ t
      · exact ⟨.terminal node hStop⟩
      · have hnStep : Ns ≤ (Fintype.card (Survivors A) : ℝ) :=
          (le_max_left _ _).trans (lt_of_not_ge hStop).le
        let μA := restrictedWeights μ A
        let ρA := globalRawProfileError 4 E β (Fintype.card (Survivors A)) r
        have hμA : ∀ S, IsAllowed (restrictedHost H A) F S →
            0 ≤ μA S ∧ μA S ≤ (2 * C) / Fintype.card (Survivors A) := by
          intro S hS
          have hs := hRawPrepared.1 S hS
          have hLow : 0 ≤ ((1 - ρA) / C) / Fintype.card (Survivors A) := by
            apply div_nonneg (div_nonneg (by dsimp [ρA]; linarith) hC.le) (by positivity)
          have hUpper : (1 + ρA) * C ≤ 2 * C :=
            mul_le_mul_of_nonneg_right (by dsimp [ρA]; linarith) hC.le
          exact ⟨hLow.trans hs.1, hs.2.trans (div_le_div_of_nonneg_right hUpper (by positivity))⟩
        obtain ⟨hηpos, hηlt, W, hWmin, hShrink, h3W, hCleanW, hSizes, hProfile, hRoute, hPaths, hInter⟩ :=
          hStep (restrictedHost H A) F r hr hnStep h3Prepared hCleanPrepared
            ρA (by dsimp [ρA]; linarith) μA hμA hRawPrepared.2
        have hWM : M ≤ W.card := by omega
        have hWMR : (M : ℝ) ≤ W.card := by exact_mod_cast hWM
        have hChildFloor := hFloor W.card r hWMR hr
        have hChild3 := commonNbrCond_mono h3W (show α₀ / 4 ≤ _ by linarith)
        have hChild4 := hingeCond_mono hCleanW.hingeCond (show α₀ / 4 ≤ _ by linarith)
        have hChildOrder : nPrep ≤ Fintype.card (Survivors (univ \ W)) := by
          rw [CorePaid.card_survivors_compl]
          exact hMprep.trans hWM
        have hChildQuot := hQuot (restrictedHost (restrictedHost H A) (univ \ W)) F
          hChildOrder hChild3 hChild4
        have hChildIndex := physicalPotential_le _ F d T hChildQuot.1 hChildQuot.2
        have hParentQuot := hQuot (restrictedHost H A) F (hMprep.trans hMA) h3base hCleanbase.hingeCond
        have hw1 : 3 < κ * W.card := hW1.trans_le (mul_le_mul_of_nonneg_left hWMR hκ.le)
        have hw2 : (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 ≤ κ / 2 * W.card :=
          hW2.trans (mul_le_mul_of_nonneg_left hWMR (by positivity))
        have hNext := physicalPotential_sample_mono (restrictedHost H A) F W κ h T hκ
          hInter hw1 hw2 hParentQuot.2
        rw [hpA] at hNext
        have hPrefix : (∑ j ∈ range r, β j) ≤
            ∑ j ∈ range (physicalPotential (restrictedHost (restrictedHost H A) (univ \ W)) F T), β j :=
          sum_le_sum_of_subset_of_nonneg (range_mono hNext) (by intro j _ _; exact hβ j)
        have hWeaken : globalGeometryFloor α₀ h D β W.card
            (physicalPotential (restrictedHost (restrictedHost H A) (univ \ W)) F T) ≤
            globalGeometryFloor α₀ h D β W.card r := by
          dsimp [globalGeometryFloor]
          nlinarith [mul_le_mul_of_nonneg_left hPrefix hD.le]
        have hShrinkA : 16 * W.card ≤ Fintype.card (Survivors A) := by
          simpa only [← Nat.card_eq_fintype_card] using hShrink
        have hWlt : W.card < n := by omega
        have hRawChild := raw_profile_sample_global (restrictedHost H A) F C E q β μA r
          (physicalPotential (restrictedHost (restrictedHost H A) (univ \ W)) F T) W
          hC hE.le hq hβ hAPos hηlt hRawPrepared (by linarith) hSizes.1 hSizes.2.le
          hShrink hNext hProfile
        obtain ⟨tail⟩ := ih W.card hWlt (restrictedHost (restrictedHost H A) (univ \ W))
          (CorePaid.card_survivors_compl W) hWmin hChildIndex
          (by simpa only [CorePaid.card_survivors_compl] using commonNbrCond_mono h3W hWeaken)
          (by simpa only [CorePaid.card_survivors_compl] using hCleanW.mono hWeaken)
          (survivorSampledWeights μA W q)
          (by simpa only [CorePaid.card_survivors_compl] using hRawChild)
        exact ⟨.descend node W hWmin hShrink hRoute hPaths hInter hNext tail⟩
  intro V _ H hn h3 hClean μ hRawInitial
  have hOrder : nPrep ≤ Fintype.card V := hMprep.trans (by omega)
  have hBounds := hQuot H F hOrder
    (commonNbrCond_mono h3 (show α₀ / 4 ≤ α₀ by linarith))
    (hingeCond_mono hClean.hingeCond (show α₀ / 4 ≤ α₀ by linarith))
  have hp := physicalPotential_le H F d T hBounds.1 hBounds.2
  have hNonneg : 0 ≤ D * ∑ j ∈ range (physicalPotential H F T), β j :=
    mul_nonneg hD.le (sum_nonneg (by intro j _; exact hβ j))
  have hFloorLe : globalGeometryFloor α₀ h D β (Fintype.card V) (physicalPotential H F T) ≤ α₀ := by
    exact (sub_le_self _ hNonneg).trans (geometryFloor_le α₀ h _ hα.le)
  exact hAll (Fintype.card V) H rfl hn hp (commonNbrCond_mono h3 hFloorLe)
    (hClean.mono hFloorLe) μ hRawInitial

#print axioms IntrinsicRawPathsPreparedVortex.terminalOrder_bounds
#print axioms IntrinsicRawPathsPreparedVortex.terminalOrder_forgetPaths
#print axioms exists_intrinsic_raw_paths_prepared_vortex
end TypedTriangle.Vortex
