/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexUniformRoutePreparation
public import RequestProject.TypedTriangle.VortexPreparedSampledCore
public import RequestProject.TypedTriangle.VortexSampleRenormalize
public import RequestProject.TypedTriangle.VortexSampleOutFromPools
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The preparation cut is chosen after the route tolerance and before the
host. The resulting prepared sample and its ambient route/profile use the
same vertex window. This does not yet build a bank on that window. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex

theorem uniform_prepared_sample_before_bank {I : Type} (F : Set (Multiset I))
    (α q C ξ : ℝ) (h N : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hC : 1 ≤ C) (hξ : 0 < ξ) (hh : 6 ≤ h) :
    ∃ (t : ℕ) (ε τ β : ℝ), Odd t ∧ 3 ≤ t ∧
      0 < ε ∧ 0 < τ ∧ τ ≤ ε / 2 ∧ τ ≤ q / 8 ∧
      0 < q - 2 * τ ∧
      τ * C / q ≤ ξ / 2 ∧ 0 < β ∧
      ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V]
        (H : Host V I) (φ : Finset V → ℝ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → CommonNbrCond H F α →
        HingeCond H F α h →
        ∃ (W : Finset V) (A : Finset (Survivors (univ \ W))),
          let Aamb := liftVertexSet (univ \ W) A
          q * Fintype.card V / 2 ≤ W.card ∧
          (W.card : ℝ) < 2 * q * Fintype.card V ∧
          (Aamb.card : ℝ) ≤ τ * Fintype.card V ∧
          CommonNbrCond
            (restrictedHost (restrictedHost H (univ \ W)) A) F
            ((α * q ^ h / 2) / 2) ∧
          HingeCond
            (restrictedHost (restrictedHost H (univ \ W)) A) F
            ((α * q ^ h / 2) / 2) h ∧
          Dispersal.PreparedCore
            (restrictedHost (restrictedHost H (univ \ W)) A).G
            (restrictedHost (restrictedHost H (univ \ W)) A).lab
            F ((α * q ^ h / 2) / 4) h N β ∧
          S07V27.RouteProp H.G H.lab F t (ε / 2) (W \ Aamb) ∧
          (∀ u v : V, u ≠ v → ∀ k : I,
            ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
            (q - 2 * τ) * (α / 2) * Fintype.card V / 2 ≤
              ((commonNbrs H k u v) ∩ (W \ Aamb)).card) ∧
          Nonempty (TypedTriangle.SampleOut H F (W \ Aamb).card 0) ∧
          ∀ u v, H.G.Adj u v →
            |S07V48.sampW H.G H.lab F φ (W \ Aamb) u v / q - 1| ≤
              ξ + τ * C / q := by
  obtain ⟨t, ε, θ, ht, ht3, hε, hθ, hUniform⟩ :=
    CorePaid.native_shared_core_preparation_route_before_tau
      α q C ξ h hα hq hq1 hC hξ hh
  let τ := min (ε / 4) (min (q / 8) (min (q * α / 8) (ξ * q / (2 * C))))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτroute : τ ≤ ε / 2 := by
    have hx : τ ≤ ε / 4 := min_le_left _ _
    linarith
  have hτpool : 4 * τ ≤ q * α := by
    have hx : τ ≤ q * α / 8 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hτprofileCap : τ * C / q ≤ ξ / 2 := by
    have hCpos : 0 < C := by linarith
    have hc : τ ≤ ξ * q / (2 * C) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    apply (div_le_iff₀ hq).2
    have heq : q * (ξ / 2) = (ξ * q / (2 * C)) * C := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hc hCpos.le]
  have hτq : τ ≤ q / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hqTrim : 0 < q - 2 * τ := by
    linarith
  let δProfile := τ * C / q
  have hδProfile : 0 < δProfile := by dsimp [δProfile]; positivity
  have hαCore : 0 < α * q ^ h / 2 := by positivity
  have hCnonneg : 0 ≤ C := by linarith
  have hτprofile : τ * C ≤ q * δProfile := by
    dsimp [δProfile]
    have hEq : q * (τ * C / q) = τ * C := by field_simp
    exact hEq.ge
  obtain ⟨β, hβ, nPrep, hPrep⟩ :=
    prepare_sampled_core_with_ambient_contract
      (α * q ^ h / 2) τ q C ε δProfile h N t
      hαCore hτ hq hCnonneg hε.le hτroute hτprofile
  obtain ⟨δWithdraw, nUniform, hδWithdraw, hWindow⟩ := hUniform τ hτ
  let n₀ := max nUniform (max ⌈2 * (nPrep : ℝ) / q⌉₊ ⌈4 / ε⌉₊)
  refine ⟨t, ε, τ, β, ht, ht3, hε, hτ, hτroute, hτq, hqTrim,
    hτprofileCap, hβ, n₀, ?_⟩
  intro V _ H φ hn hSeed hPhys h3 h4
  have hnUniform : nUniform ≤ Fintype.card V :=
    (le_max_left _ _).trans hn
  obtain ⟨W, hWlo, hWhi, _hCt, hRoute, _hGood, hPool, hRaw,
    hCore3, hCore4, _hWithdraw⟩ :=
    hWindow H F φ h3 h4 hPhys hSeed hnUniform
  have hnCeil : ⌈2 * (nPrep : ℝ) / q⌉₊ ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnε : ⌈4 / ε⌉₊ ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnCeilR : (⌈2 * (nPrep : ℝ) / q⌉₊ : ℝ) ≤ Fintype.card V := by
    exact_mod_cast hnCeil
  have hPrepSize : nPrep ≤ Fintype.card (Survivors (univ \ W)) := by
    rw [CorePaid.card_survivors_compl]
    have hbound : 2 * (nPrep : ℝ) ≤ (⌈2 * (nPrep : ℝ) / q⌉₊ : ℝ) * q :=
      (div_le_iff₀ hq).mp (Nat.le_ceil _)
    have hscale := mul_le_mul_of_nonneg_left hnCeilR hq.le
    exact_mod_cast (show (nPrep : ℝ) ≤ W.card by nlinarith [hWlo])
  have hφbound : ∀ T, IsAllowed H F T →
      0 ≤ φ T ∧ φ T ≤ C / Fintype.card V := by
    intro T hT
    have h := hSeed.1 T hT
    have hnV : 0 < (Fintype.card V : ℝ) := by
      have hw : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
      nlinarith [hWhi]
    have hz : 0 ≤ 1 / (C * Fintype.card V) := by positivity
    exact ⟨hz.trans h.1, h.2⟩
  obtain ⟨A, hA, h3A, h4A, hPc, hRouteA, hRawA⟩ :=
    hPrep H F φ ξ W hPrepSize hCore3 hCore4 hRoute hφbound hRaw
  have hPool' : ∀ u v : V, u ≠ v → ∀ k : I,
      ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
      q * α * Fintype.card V / 2 ≤ ((commonNbrs H k u v) ∩ W).card := by
    simpa only [commonNbrs, SparseEdge.commonNbrs] using hPool
  have hPoolTrim := completion_pool_after_trim H F W
    (liftVertexSet (univ \ W) A) q α τ hα hτ.le hτpool hA hPool'
  have hnNat : 0 < Fintype.card V := by
    have hw : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
    have hv : 0 < (Fintype.card V : ℝ) := by nlinarith [hWhi]
    exact_mod_cast hv
  have hlarge : 2 ≤ ⌊(ε / 2) * Fintype.card V⌋₊ := by
    apply Nat.le_floor
    have hnεR : (⌈4 / ε⌉₊ : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hnε
    calc
      (2 : ℝ) = (ε / 2) * (4 / ε) := by field_simp; ring
      _ ≤ (ε / 2) * ⌈4 / ε⌉₊ :=
        mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)
      _ ≤ (ε / 2) * Fintype.card V :=
        mul_le_mul_of_nonneg_left hnεR (by positivity)
  have hGoodTrim : ∀ v, TypedTriangle.GoodRoot H F
      (W \ liftVertexSet (univ \ W) A) v := by
    intro v
    exact TypedTriangle.RawReference.route_goodRoot H F ht3 ht
      (by positivity) hlarge hRouteA v
  have hPoolTrim' : ∀ u v : V, u ≠ v → ∀ k : I,
      ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
      (q - 2 * τ) * (α / 2) * Fintype.card V / 2 ≤
        ((SparseEdge.commonNbrs H.G H.lab k u v) ∩
          (W \ liftVertexSet (univ \ W) A)).card := by
    simpa only [commonNbrs, SparseEdge.commonNbrs] using hPoolTrim
  have hSampleOut : TypedTriangle.SampleOut H F
      (W \ liftVertexSet (univ \ W) A).card 0 :=
    sampleOut_of_goodRoots_and_pools H F
      (W \ liftVertexSet (univ \ W) A) (q - 2 * τ) (α / 2)
      hqTrim (by positivity) hnNat hGoodTrim hPoolTrim'
  exact ⟨W, A, hWlo, hWhi, hA, h3A, h4A, hPc, hRouteA,
    hPoolTrim, ⟨hSampleOut⟩, hRawA⟩

#print axioms uniform_prepared_sample_before_bank

end TypedTriangle.Vortex
