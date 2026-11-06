/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexPreparedCoreSmall
public import RequestProject.TypedTriangle.VortexSubtypeLift
public import RequestProject.TypedTriangle.VortexSampleTrimming
public import RequestProject.TypedTriangle.RawProfileDeletion
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Prepare inside a sampled core, while retaining the route and completion
profile on the original ambient graph. No paid-edge stability is asserted. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem prepare_sampled_core_with_ambient_contract
    (α τ q b ε δ : ℝ) (h N t : ℕ)
    (hα : 0 < α) (hτ : 0 < τ) (hq : 0 < q) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (hτroute : τ ≤ ε/2) (hτprofile : τ*b ≤ q*δ) :
    ∃ β : ℝ, 0 < β ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (μ : Finset V → ℝ) (e : ℝ)
        (W : Finset V),
        n₀ ≤ Fintype.card (Survivors (univ \ W)) →
        CommonNbrCond (restrictedHost H (univ \ W)) F α →
        HingeCond (restrictedHost H (univ \ W)) F α h →
        S07V27.RouteProp H.G H.lab F t ε W →
        (∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b/Fintype.card V) →
        (∀ u v, H.G.Adj u v →
          |S07V48.sampW H.G H.lab F μ W u v/q - 1| ≤ e) →
        ∃ A : Finset (Survivors (univ \ W)),
          let Aamb := liftVertexSet (univ \ W) A
          (Aamb.card : ℝ) ≤ τ * Fintype.card V ∧
          CommonNbrCond (restrictedHost (restrictedHost H (univ \ W)) A) F (α/2) ∧
          HingeCond (restrictedHost (restrictedHost H (univ \ W)) A) F (α/2) h ∧
          Dispersal.PreparedCore
            (restrictedHost (restrictedHost H (univ \ W)) A).G
            (restrictedHost (restrictedHost H (univ \ W)) A).lab
            F (α/4) h N β ∧
          S07V27.RouteProp H.G H.lab F t (ε/2) (W \ Aamb) ∧
          ∀ u v, H.G.Adj u v →
            |S07V48.sampW H.G H.lab F μ (W \ Aamb) u v/q - 1| ≤ e+δ := by
  obtain ⟨β,hβ,nCore,hcore⟩ :=
    preparedCore_with_small_geometry_of_H3H4 α τ h N hα hτ
  refine ⟨β,hβ,max nCore 1,?_⟩
  intro V I _ H F μ e W hn h3 h4 hroute hμ hprofile
  let Z := (univ : Finset V) \ W
  let H0 := restrictedHost H Z
  have hnCore : nCore ≤ Fintype.card (Survivors Z) :=
    (le_max_left _ _).trans hn
  obtain ⟨A,hA,h3A,h4A,hpc⟩ := hcore H0 F hnCore h3 h4
  let Aamb := liftVertexSet Z A
  have hcA : Aamb.card = A.card := card_liftVertexSet Z A
  have hcard : Fintype.card (Survivors Z) ≤ Fintype.card V :=
    Fintype.card_subtype_le _
  have hAamb : (Aamb.card : ℝ) ≤ τ * Fintype.card V := by
    have hc : (Fintype.card (Survivors Z) : ℝ) ≤ Fintype.card V :=
      by exact_mod_cast hcard
    have ht := mul_le_mul_of_nonneg_left hc hτ.le
    rw [hcA]
    exact hA.trans ht
  have hnV : 0 < (Fintype.card V : ℝ) := by
    have hOne : 1 ≤ Fintype.card (Survivors Z) := (le_max_right _ _).trans hn
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hOne.trans hcard)
  have hAroute : (Aamb.card : ℝ) ≤ ε/2 * Fintype.card V :=
    hAamb.trans (mul_le_mul_of_nonneg_right hτroute hnV.le)
  have hAbudget : (Aamb.card : ℝ) * (b/Fintype.card V) ≤ q*δ := by
    have hmul := mul_le_mul_of_nonneg_right hAamb hb
    calc
      (Aamb.card : ℝ) * (b/Fintype.card V) = Aamb.card*b/Fintype.card V := by ring
      _ ≤ τ*b := by
        apply (div_le_iff₀ hnV).mpr
        nlinarith [hmul]
      _ ≤ q*δ := hτprofile
  refine ⟨A, hAamb, ?_, ?_, ?_,
    routeProp_sdiff hε hroute Aamb hAroute, ?_⟩
  · dsimp only [H0, Z] at h3A
    convert h3A using 1 <;> exact Subsingleton.elim _ _
  · dsimp only [H0, Z] at h4A
    convert h4A using 1 <;> exact Subsingleton.elim _ _
  · dsimp only [H0, Z] at hpc
    convert hpc using 1 <;> exact Subsingleton.elim _ _
  · intro u v huv
    exact RawReference.sampled_profile_after_vertex_deletion H F μ W Aamb u v
      b q e δ hb hq hnV hμ (hprofile u v huv) hAbudget

#print axioms prepare_sampled_core_with_ambient_contract

end TypedTriangle.Vortex
