/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexIntrinsicPreparationKernel
public import RequestProject.TypedTriangle.VortexIntrinsicRawPreparedVortex
public import RequestProject.TypedTriangle.VortexAutomaticCleanRawQuarticTests
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open RawReference CorePaid

/-- Outer preparation and one joint sample. Extra events are evaluated on
this very sample, so ambient-root tests may be supplied after the actual
trim is known. This intermediate lemma does not construct their tails. -/
theorem outer_raw_prepared_sample_with_tests_rich {I : Type} (F : Set (Multiset I))
    (α C ε : ℝ) (h d T : ℕ) (K : IntrinsicPreparationKernel (α / 4) h ε d T)
    (hα : 0 < α) (hC : 0 < C) (hh : 1 ≤ h)
    (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (hBudget : (∑ j ∈ range (d + (d + 1) * Nat.log 2 T + 1), β j) ≤
      min ε (min (α / (4 * (2 : ℝ)^Nat.choose h 2)) (1 / (8 * max 1 (2 * C)))))
    (N Mrequired : ℕ) (q θExtra : ℝ) (hq : 0 < q) (hq32 : q ≤ 1 / 32) (hθ : 0 < θExtra) :
    ∃ nRoot : ℕ, ∀ {V : Type} [Fintype V] (H : Host V I), nRoot ≤ Fintype.card V →
      CommonNbrCond H F (8 * α) → CleanHingeCond H F (8 * α) h →
      ∀ μ : Finset V → ℝ, IsDiffuseSeed H F C μ →
      ∃ node : IntrinsicRawPreparedLayer H F α C β h N Mrequired d T μ,
        CommonNbrCond (restrictedHost H node.trim) F (4 * α) ∧
        CleanHingeCond (restrictedHost H node.trim) F (4 * α) h ∧
        letI : DecidableEq (Survivors node.trim) := Classical.decEq _
        ∀ {J : Type*} [Fintype J], Fintype.card J ≤ Fintype.card (Survivors node.trim)^4 →
        ∀ Eextra : J → Finset (Survivors node.trim) → Prop,
          (∀ j, bprob q univ (Eextra j) ≤ Real.exp (-(θExtra * Fintype.card (Survivors node.trim)))) →
        ∃ W : Finset (Survivors node.trim), Mrequired ≤ W.card ∧
          16 * W.card ≤ Fintype.card (Survivors node.trim) ∧
          q * Fintype.card (Survivors node.trim) / 2 ≤ W.card ∧
          (W.card : ℝ) < 2 * q * Fintype.card (Survivors node.trim) ∧
          (1 - automaticRelativeError (Fintype.card (Survivors node.trim))) * q *
            Fintype.card (Survivors node.trim) ≤ (W.card : ℝ) ∧
          (W.card : ℝ) < (1 + automaticRelativeError (Fintype.card (Survivors node.trim))) * q *
            Fintype.card (Survivors node.trim) ∧
          CommonNbrCond (restrictedHost (restrictedHost H node.trim) (univ \ W)) F α ∧
          CleanHingeCond (restrictedHost (restrictedHost H node.trim) (univ \ W)) F α h ∧
          physicalPotential (restrictedHost (restrictedHost H node.trim) (univ \ W)) F T ≤
            d + (d + 1) * Nat.log 2 T ∧
          node.index ≤ physicalPotential (restrictedHost (restrictedHost H node.trim) (univ \ W)) F T ∧
          RawProfileAt (restrictedHost (restrictedHost H node.trim) (univ \ W)) F C
            (globalRawProfileError 4 (max 1 (2 * C)) β
              (Fintype.card (Survivors (univ \ W)))
              (physicalPotential (restrictedHost (restrictedHost H node.trim) (univ \ W)) F T))
            (survivorSampledWeights (restrictedWeights μ node.trim) W q) ∧
          ∀ j, ¬ Eextra j W := by
  let D : ℝ := 2 ^ Nat.choose h 2
  let E : ℝ := max 1 (2 * C)
  let L := d + (d + 1) * Nat.log 2 T
  have hD : 0 < D := by positivity
  have hE1 : 1 ≤ E := le_max_left _ _
  have hEC : 2 * C ≤ E := le_max_right _ _
  have hE : 0 < E := by linarith
  have hq1 : q ≤ 1 := by linarith
  obtain ⟨nPrep, hQuot, hPrepare⟩ := K N
  obtain ⟨Ns, hSample⟩ := exists_automatic_clean_raw_profile_quartic_tests_uniform
    (4 * α) q (2 * C) θExtra h (by positivity) hq hq1 (by positivity) hθ
  let κ : ℝ := α * q^h
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let R : ℝ := max ((4 * ((h : ℝ) + 1))^4)
    (max ((32 : ℝ)^4) (max (4 / κ) (2 * (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 / κ)))
  let M := max (max nPrep Mrequired) (max 1 (⌈R⌉₊ + 1))
  have hMprep : nPrep ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMreq : Mrequired ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hM1 : 1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hRM : R ≤ (M : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈R⌉₊ ≤ M from (Nat.le_succ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hPower : (4 * ((h : ℝ) + 1))^4 ≤ M := (le_max_left _ _).trans hRM
  have hRawPower : (32 : ℝ)^4 ≤ M := ((le_max_left _ _).trans (le_max_right _ _)).trans hRM
  have hWin1 : 3 < κ * M := by
    have hs : 4 / κ ≤ (M : ℝ) :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hRM
    have hc := (div_le_iff₀ hκ).mp hs
    linarith
  have hWin2 : (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 ≤ κ / 2 * M := by
    have hs : 2 * (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 / κ ≤ (M : ℝ) :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hRM
    have hc := (div_le_iff₀ hκ).mp hs
    nlinarith
  let Gate : ℝ := max Ns (max M (2 * M / q))
  let nRoot := 2 * ⌈Gate⌉₊ + 2
  have hGate : Gate ≤ (nRoot : ℝ) / 2 := by
    have hc := Nat.le_ceil Gate
    dsimp [nRoot]
    push_cast
    linarith
  have hMgate : (M : ℝ) ≤ Gate := (le_max_left _ _).trans (le_max_right _ _)
  have hMroot : (M : ℝ) ≤ nRoot := by
    have hc : (0 : ℝ) ≤ nRoot := by positivity
    linarith [hMgate.trans hGate]
  have hBudgetK : (∑ j ∈ range (L + 1), β j) ≤ ε := hBudget.trans (min_le_left _ _)
  have hBudgetD : D * (∑ j ∈ range (L + 1), β j) ≤ α / 4 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 4 * D)).mp
      (hBudget.trans ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith
  have hBudgetE : E * (∑ j ∈ range (L + 1), β j) ≤ 1 / 8 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 8 * E)).mp
      (hBudget.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith
  have hRawCap (n : ℝ) (r : ℕ) (hn : (M : ℝ) ≤ n) (hr : r ≤ L) :
      globalRawProfileError 4 E β n r ≤ 1 / 4 := by
    have he := automaticRelativeError_le_of_power_bound 32 n (by norm_num) (hRawPower.trans hn)
    norm_num at he
    have hp : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range (L + 1), β j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intro j _ _; exact hβ j)
    apply globalRawProfileError_le_cap 4 E (1 / 4) β n r
    · linarith
    · norm_num
      exact (mul_le_mul_of_nonneg_left hp hE.le).trans hBudgetE
  refine ⟨nRoot, ?_⟩
  intro V _ H hn h3 hClean μ hSeed
  have hnR : (nRoot : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hMcurR : (M : ℝ) ≤ Fintype.card V := hMroot.trans hnR
  have hMcur : M ≤ Fintype.card V := by exact_mod_cast hMcurR
  have hQroot := hQuot H F (hMprep.trans hMcur)
    (commonNbrCond_mono h3 (show α / 4 ≤ 8 * α by linarith))
    (hingeCond_mono hClean.hingeCond (show α / 4 ≤ 8 * α by linarith))
  have hpRoot := physicalPotential_le H F d T hQroot.1 hQroot.2
  obtain ⟨r, hr, A, hpEnter, hpA, hCost, hHalf, h3A, hCleanA, hPc⟩ :=
    hPrepare β hβ hBudgetK H F (8 * α) (hMprep.trans hMcur) (by linarith) h3 hClean
  letI : DecidableEq (Survivors A) := Classical.decEq _
  have hAgate : Gate ≤ (Fintype.card (Survivors A) : ℝ) := by linarith
  have hMAR : (M : ℝ) ≤ Fintype.card (Survivors A) := hMgate.trans hAgate
  have hMA : M ≤ Fintype.card (Survivors A) := by exact_mod_cast hMAR
  have hAPos : (0 : ℝ) < Fintype.card (Survivors A) := by
    exact_mod_cast (show 0 < Fintype.card (Survivors A) by omega)
  have hnPos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  let debt := (∑ j ∈ range r, β j) - ∑ j ∈ range (physicalPotential H F T), β j
  have hDebt0 : 0 ≤ debt := by
    have hs := sum_le_sum_of_subset_of_nonneg (range_mono hpEnter) (by intro j _ _; exact hβ j)
    dsimp [debt]
    linarith
  have hDebtTotal : debt ≤ ∑ j ∈ range (L + 1), β j := by
    have hs : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range (L + 1), β j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intro j _ _; exact hβ j)
    have hp0 : 0 ≤ ∑ j ∈ range (physicalPotential H F T), β j := sum_nonneg (by intro j _; exact hβ j)
    dsimp [debt]
    linarith
  have hLoss := (mul_le_mul_of_nonneg_left hDebtTotal hD.le).trans hBudgetD
  have hStrong : 4 * α ≤ 8 * α - D * debt := by linarith
  have h3Strong := commonNbrCond_mono h3A hStrong
  have hCleanStrong := hCleanA.mono hStrong
  have hDebt1 : debt < 1 := by
    have hs := (mul_le_mul_of_nonneg_left hDebtTotal hE.le).trans hBudgetE
    have hc := mul_le_mul_of_nonneg_right hE1 hDebt0
    nlinarith
  have hInitial := (RawProfileAt.of_seed hSeed).mono hC.le
    (globalRawProfileError_nonneg E β hE.le hβ (Fintype.card V) (physicalPotential H F T))
  have hRawA := raw_profile_restrict_global H F C E β μ (physicalPotential H F T) r A debt
    hC hE1 hEC hβ hnPos hInitial (by linarith [hRawCap _ _ hMcurR hpRoot]) hDebt0 hDebt1
    (by dsimp [debt]; nlinarith [hCost]) le_rfl
  have hCapA := hRawCap (Fintype.card (Survivors A)) r hMAR hr
  let baseNode : IntrinsicPreparedLayer H F α β h N Mrequired d T :=
    ⟨A, r, hr, hpEnter, hpA, hCost,
      commonNbrCond_mono h3Strong (by linarith), hCleanStrong.mono (by linarith),
      hPc, hMreq.trans hMA⟩
  let node : IntrinsicRawPreparedLayer H F α C β h N Mrequired d T μ := ⟨baseNode, hRawA, hCapA⟩
  refine ⟨node, h3Strong, hCleanStrong, ?_⟩
  intro J _ hJ Eextra hExtra
  let μA := restrictedWeights μ A
  let ρA := globalRawProfileError 4 E β (Fintype.card (Survivors A)) r
  have hμA : ∀ S, IsAllowed (restrictedHost H A) F S →
      0 ≤ μA S ∧ μA S ≤ (2 * C) / Fintype.card (Survivors A) := by
    intro S hS
    have hs := hRawA.1 S hS
    have hLo : 0 ≤ ((1 - ρA) / C) / Fintype.card (Survivors A) :=
      div_nonneg (div_nonneg (by dsimp [ρA]; linarith) hC.le) (by positivity)
    have hHi : (1 + ρA) * C ≤ 2 * C := mul_le_mul_of_nonneg_right (by dsimp [ρA]; linarith) hC.le
    exact ⟨hLo.trans hs.1, hs.2.trans (div_le_div_of_nonneg_right hHi (by positivity))⟩
  have hnSample : Ns ≤ (Fintype.card (Survivors A) : ℝ) := (le_max_left _ _).trans hAgate
  obtain ⟨hηpos, hηlt, W, hWlo, hWhi, hPool, hHinge, hProfile, hAvoid⟩ :=
    hSample (restrictedHost H A) F (4 * α) ρA le_rfl (by dsimp [ρA]; linarith)
      hnSample h3Strong hCleanStrong μA hμA hRawA.2 hJ Eextra hExtra
  change (1 - automaticRelativeError (Fintype.card (Survivors A))) * q *
    Fintype.card (Survivors A) ≤ (W.card : ℝ) at hWlo
  change (W.card : ℝ) < (1 + automaticRelativeError (Fintype.card (Survivors A))) * q *
    Fintype.card (Survivors A) at hWhi
  have hErr := automaticRelativeError_le_of_power_bound (4 * ((h : ℝ) + 1))
    (Fintype.card (Survivors A)) (by positivity) (hPower.trans hMAR)
  have hηhalf : automaticRelativeError (Fintype.card (Survivors A)) ≤ 1 / 2 := by
    have hb : (2 : ℝ) ≤ 4 * ((h : ℝ) + 1) := by nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
    exact hErr.trans (by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hb)
  have hηcost : ((h : ℝ) + 1) * automaticRelativeError (Fintype.card (Survivors A)) ≤ 1 / 4 := by
    have hs := mul_le_mul_of_nonneg_left hErr (by positivity : 0 ≤ (h : ℝ) + 1)
    have heq : ((h : ℝ) + 1) * (4 * ((h : ℝ) + 1))⁻¹ = (1 / 4 : ℝ) := by field_simp
    rwa [heq] at hs
  have hScale : 2 * (M : ℝ) / q ≤ Fintype.card (Survivors A) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hAgate
  have hWminR : (M : ℝ) ≤ W.card := by
    have hs := (div_le_iff₀ hq).mp hScale
    have hp := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤
      1 - automaticRelativeError (Fintype.card (Survivors A)) by linarith) (mul_nonneg hq.le hAPos.le)
    nlinarith [hWlo]
  have hWmin : M ≤ W.card := by exact_mod_cast hWminR
  have hWposR : (0 : ℝ) < W.card := by exact_mod_cast (show 0 < W.card by omega)
  have hUpper : (W.card : ℝ) < 2 * q * Fintype.card (Survivors A) := by
    have hs := mul_lt_mul_of_pos_right (show
      1 + automaticRelativeError (Fintype.card (Survivors A)) < 2 by linarith)
      (mul_pos hq hAPos)
    exact hWhi.trans (by convert hs using 1 <;> ring)
  have hShrinkR : (16 : ℝ) * W.card ≤ Fintype.card (Survivors A) := by
    have hs := mul_le_mul_of_nonneg_right (show 32 * q ≤ 1 by linarith) hAPos.le
    nlinarith
  have hShrink : 16 * W.card ≤ Fintype.card (Survivors A) := by exact_mod_cast hShrinkR
  have hGeo := clean_relative_sample_child_geometry (restrictedHost H A) F (by positivity : 0 < 4 * α)
    hq hηpos.le hηlt hh hCleanStrong W hWhi.le hPool hHinge
  have hParam : α ≤ (4 * α) * (1 - ((h : ℝ) + 1) * automaticRelativeError (Fintype.card (Survivors A))) := by nlinarith
  have h3Child := commonNbrCond_mono hGeo.1 hParam
  have hCleanChild := hGeo.2.mono hParam
  have hChildLarge : nPrep ≤ Fintype.card (Survivors (univ \ W)) := by
    rw [CorePaid.card_survivors_compl]
    exact hMprep.trans hWmin
  have hQchild := hQuot (restrictedHost (restrictedHost H A) (univ \ W)) F hChildLarge
    (commonNbrCond_mono h3Child (by linarith)) (hingeCond_mono hCleanChild.hingeCond (by linarith))
  have hChildIndex := physicalPotential_le _ F d T hQchild.1 hQchild.2
  have hInter : ∀ U : Finset (Survivors A), W ⊆ U →
      CommonNbrCond (restrictedHost (restrictedHost H A) (univ \ U)) F κ ∧
      HingeCond (restrictedHost (restrictedHost H A) (univ \ U)) F κ h := by
    intro U hWU
    have hi := anchored_clean_intermediate_geometry (restrictedHost H A) F (by positivity : 0 < 4 * α)
      hq hq1 hηlt hh hCleanStrong W U hWU hPool hHinge
    have hc : κ ≤ (1 - automaticRelativeError (Fintype.card (Survivors A))) * (4 * α) * q^h := by
      have hs := mul_le_mul_of_nonneg_right (show α ≤
        (1 - automaticRelativeError (Fintype.card (Survivors A))) * (4 * α) by nlinarith) (pow_nonneg hq.le h)
      exact hs
    exact ⟨commonNbrCond_mono hi.1 hc, hingeCond_mono hi.2.hingeCond hc⟩
  have hQparent := hQuot (restrictedHost H A) F (hMprep.trans hMA)
    (commonNbrCond_mono h3Strong (by linarith)) (hingeCond_mono hCleanStrong.hingeCond (by linarith))
  have hw1 : 3 < κ * W.card := hWin1.trans_le (mul_le_mul_of_nonneg_left hWminR hκ.le)
  have hw2 : (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 ≤ κ / 2 * W.card :=
    hWin2.trans (mul_le_mul_of_nonneg_left hWminR (by positivity))
  have hNext := physicalPotential_sample_mono (restrictedHost H A) F W κ h T hκ hInter hw1 hw2 hQparent.2
  rw [hpA] at hNext
  have hRawChild := raw_profile_sample_global (restrictedHost H A) F C E q β μA r
    (physicalPotential (restrictedHost (restrictedHost H A) (univ \ W)) F T) W hC hE.le hq hβ
    hAPos hηlt hRawA (by linarith) hWlo hWhi.le hShrink hNext hProfile
  have hWlo' : q * Fintype.card (Survivors A) / 2 ≤ (W.card : ℝ) := by
    have hs := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤
      1 - automaticRelativeError (Fintype.card (Survivors A)) by linarith) (mul_nonneg hq.le hAPos.le)
    nlinarith [hWlo]
  have hWhi' : (W.card : ℝ) < 2 * q * Fintype.card (Survivors A) := hUpper
  exact ⟨W, hMreq.trans hWmin, hShrink, hWlo', hWhi', hWlo, hWhi, h3Child, hCleanChild,
    hChildIndex, hNext, hRawChild, hAvoid⟩

#print axioms outer_raw_prepared_sample_with_tests_rich
end TypedTriangle.Vortex

