/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SmoothExactification
public import RequestProject.TypedTriangle.NativeCongestion
public import RequestProject.TypedTriangle.VortexFixedSampleSeed
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A fixed prepared core admits the same smooth physical inverse used by
positive exactification. The preparation of that core is a separate gate. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.NativeSmooth

open Incidence RoutingConstants ComponentRows ActiveCover
open Grouping Dispersal S10V22

/-- Produce a uniform integer congestion certificate on the *given* prepared
host. No additional vertex deletion is made after `Pc` has been supplied. -/
theorem congestion_on_prepared_host (α β : ℝ) (h : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    ∃ L : ℝ, 0 < L ∧ ∃ N₀ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        Dispersal.PreparedCore H.G H.lab F (α / 4) h N₀ β →
        ∀ x : Sym2 V → ℤ, x ∈ lattice H F →
          ∃ cert : Finset V → ℤ,
            Dispersal.IsCert H.G H.lab F cert x ∧
            (Dispersal.l1T cert : ℝ) ≤ L * ActiveCover.norm1 H.G x ∧
            ∀ v, (Dispersal.vload cert v : ℝ) ≤ L *
              (ActiveCover.dabs H.G x v +
                ActiveCover.norm1 H.G x / Fintype.card V + 1) := by
  let γ : ℝ := α / 2
  let D := routeD γ
  let δ := routeδ γ h
  obtain ⟨s, H₀, D₀, nCmp, hcmp⟩ :=
    compression_of_H3H4 γ h (by dsimp [γ]; positivity)
  let d := (s + 1) ^ 2
  let R := 3 * D₀
  let B := D₀ * (3 * D)
  obtain ⟨K, N₀, hU⟩ := native_uniformCertOn_of_H3H4 (α / 4) h
    (3 * D * groupBound d B R) (by positivity)
  let S : ℝ := 4 * D + 3 + 32 * D / δ + 12 * K / β + 2 * D + 2
  let L : ℝ := K * S + 1
  have hδ : 0 < δ := routeδ_pos (by dsimp [γ]; positivity) h
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  let n₀ := max N₀ (max nCmp (routeN0 γ h))
  refine ⟨L, hL, N₀, n₀, ?_⟩
  intro V I _ H F hn hH3 hH4 Pc x hx
  have hnCmp : nCmp ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnRoute : routeN0 γ h ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  obtain ⟨cmp⟩ := hcmp H F hnCmp
    (commonNbrCond_mono hH3 (by dsimp [γ]; linarith))
    (hingeCond_mono hH4 (by dsimp [γ]; linarith))
  obtain ⟨coord, emb, hrec, hbox, hcoord⟩ :=
    native_compression_coordinates H F cmp (3 * D)
  have hlow : ∀ j : Row V, IsActiveRow H.G H.lab F j →
      γ * Fintype.card V ≤ j.2.card := by
    rintro ⟨a, J⟩ hJ
    exact active_component_card_ge
      (commonNbrCond_mono hH3 (by dsimp [γ]; linarith)) hJ
  have hdel : ∀ Z : Finset V, (Z.card : ℝ) ≤ δ * Fintype.card V →
      DeletionHyp H.G H.lab F Z := by
    intro Z hZ
    exact routing_deletion_of_H3H4 (by dsimp [γ]; positivity)
      (commonNbrCond_mono hH3 (by dsimp [γ]; linarith))
      (hingeCond_mono hH4 (by dsimp [γ]; linarith))
      hnRoute Z hZ
  obtain ⟨cert, hc, hnrm, hload⟩ :=
    Composition.prepared_core_composed_certificate_uniform δ d R B
      (hU F) Pc hβ hδ
      (compConst_mul_routeδ_le γ h)
      (lt_of_lt_of_le (routeN0_pos γ h) hnRoute)
      (ComponentCount.hrows_of_lower H.G H.lab F
        (by dsimp [γ]; positivity) hlow)
      (ComponentCount.hdeg_of_lower H.G H.lab F
        (by dsimp [γ]; positivity) hlow)
      hdel (one_le_routeD γ) (routeD_spec γ)
      (triBd H F) (triBd_mem_lattice H F)
      (cmp.C₀.comp (nativeLocalProfile H F))
      (cmp.P.comp (nativeLocalProfile H F))
      (native_compression_decomp H F cmp)
      coord emb hrec hbox hcoord x hx
  have hKL : (K : ℝ) * S ≤ L := by dsimp [L]; linarith
  refine ⟨cert, hc, hnrm.trans ?_, fun v => (hload v).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hKL
      (by exact_mod_cast Composition.norm1_nonneg (G := H.G) x)
  · apply mul_le_mul_of_nonneg_right hKL
    have hd : (0 : ℝ) ≤ ActiveCover.dabs H.G x v := by
      exact_mod_cast Composition.dabs_nonneg (G := H.G) x v
    have hx0 : (0 : ℝ) ≤ ActiveCover.norm1 H.G x := by
      exact_mod_cast Composition.norm1_nonneg (G := H.G) x
    positivity

/-- A prepared host has a smooth inverse on its *own* vertex set. The
prepared-core hypothesis is the obligation supplied by the adaptive vortex,
not an additional hypothesis of the final decomposition theorem. -/
theorem smooth_on_prepared_host (α β : ℝ) (h : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hh : 6 ≤ h) :
    ∃ Kinf : ℝ, 0 < Kinf ∧ ∃ N₀ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        Dispersal.PreparedCore H.G H.lab F (α / 4) h N₀ β →
        Smooth H F Kinf := by
  obtain ⟨L, hL, N₀, nNative, hcert⟩ :=
    congestion_on_prepared_host α β h hα hβ
  let nKernel : ℕ := ⌈S10V23.Proc.nZero α h⌉₊
  have hcoeff : 0 < coeff α h L := coeff_pos h hα hL.le
  refine ⟨coeff α h L, hcoeff, N₀, max nNative nKernel, ?_⟩
  intro V I _ H F hn hH3 hH4 Pc
  letI : DecidableEq V := Classical.decEq V
  have hnNative : nNative ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnKernel : nKernel ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hnK : S10V23.Proc.nZero α h ≤ (Fintype.card V : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnKernel)
  have hp : IntCertProvider (triMat (allowedTri H.G H.lab F))
      (triTw (allowedTri H.G H.lab F)) edgeEw L (Fintype.card V : ℝ) :=
    NativeReal.provider_of_native (V := V) (I := I) (G := H.G)
      (lab := H.lab) (F := F) (K := L)
      (hcert H F hnNative hH3 hH4 Pc)
  intro x hx xmax hxmax0 hxmax
  obtain ⟨w, hw, hb⟩ := S10V23.smooth_inverse_H3H4 hH3 hH4
    hα hh hnK hL.le hp hx hxmax
  exact supported_certificate H F
    (div_nonneg (mul_nonneg hcoeff.le hxmax0) (Nat.cast_nonneg _)) w hw hb

#print axioms TypedTriangle.NativeSmooth.smooth_on_prepared_host

/-- Exact H1 on the actual paid child, once the adaptive construction has
delivered a prepared core there and proved its edge indicator physical. -/
theorem exact_seed_on_prepared_child (α β C : ℝ) (h : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hh : 6 ≤ h) (hC : 1 ≤ C) :
    ∃ Kinf : ℝ, 0 < Kinf ∧ ∃ N₀ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (J : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond J F α → HingeCond J F α h →
        Dispersal.PreparedCore J.G J.lab F (α / 4) h N₀ β →
        IsPhysical J F (edges J) →
        ∀ (μ : Finset V → ℝ) (ξ : ℝ), 0 ≤ ξ →
          (∀ T, μ T ≠ 0 → IsAllowed J F T) →
          (∀ T, IsAllowed J F T →
            (1 / (2*C)) / Fintype.card V ≤ μ T ∧
              μ T ≤ (2*C) / Fintype.card V) →
          (∀ e ∈ edges J, |bdry J F μ e - 1| ≤ ξ) →
          Kinf * ξ ≤ 1 / (4*C) →
          ∃ ψ : Finset V → ℝ, IsDiffuseSeed J F (4*C) ψ := by
  obtain ⟨Kinf,hK,N₀,n₀,hSmooth⟩ :=
    smooth_on_prepared_host α β h hα hβ hh
  refine ⟨Kinf,hK,N₀,n₀,?_⟩
  intro V I _ J F hn h3 h4 Pc hPhys μ ξ hξ hμsupp hμ hload hbudget
  exact TypedTriangle.Vortex.exact_seed_on_fixed_host_of_smooth J F C Kinf ξ
    hC hξ (hSmooth J F hn h3 h4 Pc) hPhys μ hμsupp hμ hload hbudget

#print axioms TypedTriangle.NativeSmooth.exact_seed_on_prepared_child

end TypedTriangle.NativeSmooth
