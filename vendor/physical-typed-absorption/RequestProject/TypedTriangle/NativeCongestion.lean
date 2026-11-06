/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.NativeCompressionData
public import RequestProject.TypedTriangle.PreparedCoreConstruction
public import RequestProject.TypedTriangle.PreparedRouting
public import RequestProject.TypedTriangle.NativeUniformCertAdapter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Native P05 assembly. Candidate until its rc3 audit passes.
All constants precede the host; the induced core is chosen before its demands.
No compression, routing, persistence or avoiding-certificate provider is assumed.
This signed-certificate result does not assert a positive catalogue or T. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle

open Incidence RoutingConstants ComponentRows ActiveCover
open Grouping Composition Dispersal

/-- A uniformly chosen core admits physical signed certificates with a common
norm and vertex-congestion constant, from the original H3--H4 alone. -/
theorem native_congestion_with_geometry_of_H3H4 (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ L : ℝ, 0 < L ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∃ A : Finset V, (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 4 ∧
          CommonNbrCond (restrictedHost H A) F (α / 2) ∧
          HingeCond (restrictedHost H A) F (α / 2) h ∧
          ∀ x : Sym2 (Survivors A) → ℤ, x ∈ lattice (restrictedHost H A) F →
            ∃ cert : Finset (Survivors A) → ℤ,
              Dispersal.IsCert (restrictedHost H A).G (restrictedHost H A).lab F cert x ∧
              (Dispersal.l1T cert : ℝ) ≤ L * ActiveCover.norm1 (restrictedHost H A).G x ∧
              ∀ v, (Dispersal.vload cert v : ℝ) ≤ L *
                (ActiveCover.dabs (restrictedHost H A).G x v +
                  ActiveCover.norm1 (restrictedHost H A).G x / Fintype.card (Survivors A) + 1) := by
  let γ : ℝ := α / 2
  let D := routeD γ
  let δ := routeδ γ h
  obtain ⟨s, H₀, D₀, nCmp, hcmp⟩ := compression_of_H3H4 γ h (by change 0 < α / 2; positivity)
  let d := (s + 1) ^ 2
  let R := 3 * D₀
  let B := D₀ * (3 * D)
  obtain ⟨K, N₀, hU⟩ := native_uniformCertOn_of_H3H4 (α / 4) h
    (3 * D * groupBound d B R) (by positivity)
  obtain ⟨β, hβ, nEntry, hcore⟩ := preparedCore_with_geometry_of_H3H4 α h N₀ hα
  let S : ℝ := 4 * D + 3 + 32 * D / δ + 12 * K / β + 2 * D + 2
  let L : ℝ := K * S + 1
  have hδ : 0 < δ := routeδ_pos (by change 0 < α / 2; positivity) h
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, max nEntry (4 * max nCmp (routeN0 γ h) + 1), ?_⟩
  intro V I _ H F hn hH3 hH4
  obtain ⟨A, hA, hA3, hA4, Pc⟩ := hcore H F ((le_max_left _ _).trans hn) hH3 hH4
  letI : DecidableEq (Survivors A) := Classical.decEq _
  let Hc := restrictedHost H A
  have hcCard := card_survivors_add_card A
  have hcR : (Fintype.card (Survivors A) : ℝ) + A.card = Fintype.card V := by
    exact_mod_cast hcCard
  have hnlarge : 4 * max nCmp (routeN0 γ h) + 1 ≤ Fintype.card V :=
    (le_max_right _ _).trans hn
  have hnlargeR : (4 : ℝ) * max nCmp (routeN0 γ h) + 1 ≤ Fintype.card V := by
    exact_mod_cast hnlarge
  have hcLarge : max nCmp (routeN0 γ h) ≤ Fintype.card (Survivors A) := by
    exact_mod_cast (show ((max nCmp (routeN0 γ h) : ℕ) : ℝ) ≤ Fintype.card (Survivors A) by linarith)
  have hnCmp := (le_max_left _ _).trans hcLarge
  have hnRoute := (le_max_right _ _).trans hcLarge
  obtain ⟨cmp⟩ := hcmp Hc F hnCmp hA3 hA4
  obtain ⟨coord, emb, hrec, hbox, hcoord⟩ := native_compression_coordinates Hc F cmp (3 * D)
  have hlow : ∀ j : Row (Survivors A), IsActiveRow Hc.G Hc.lab F j →
      γ * Fintype.card (Survivors A) ≤ j.2.card := by
    rintro ⟨a, J⟩ hJ
    exact active_component_card_ge hA3 hJ
  have hdel : ∀ Z : Finset (Survivors A), (Z.card : ℝ) ≤ δ * Fintype.card (Survivors A) →
      DeletionHyp Hc.G Hc.lab F Z := by
    intro Z hZ
    exact routing_deletion_of_H3H4 (by change 0 < α / 2; positivity) hA3 hA4 hnRoute Z hZ
  refine ⟨A, hA, hA3, hA4, ?_⟩
  intro x hx
  obtain ⟨cert, hc, hnrm, hload⟩ :=
    Composition.prepared_core_composed_certificate_uniform δ d R B (hU F) Pc hβ hδ
      (compConst_mul_routeδ_le γ h)
      (lt_of_lt_of_le (routeN0_pos γ h) hnRoute)
      (ComponentCount.hrows_of_lower Hc.G Hc.lab F (by change 0 < α / 2; positivity) hlow)
      (ComponentCount.hdeg_of_lower Hc.G Hc.lab F (by change 0 < α / 2; positivity) hlow)
      hdel (one_le_routeD γ) (routeD_spec γ)
      (triBd Hc F) (triBd_mem_lattice Hc F)
      (cmp.C₀.comp (nativeLocalProfile Hc F)) (cmp.P.comp (nativeLocalProfile Hc F))
      (native_compression_decomp Hc F cmp) coord emb hrec hbox hcoord x hx
  have hKL : (K : ℝ) * S ≤ L := by dsimp [L]; linarith
  refine ⟨cert, hc, hnrm.trans ?_, fun v => (hload v).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hKL (by exact_mod_cast Composition.norm1_nonneg (G := Hc.G) x)
  · apply mul_le_mul_of_nonneg_right hKL
    have hd : (0 : ℝ) ≤ ActiveCover.dabs Hc.G x v := by
      exact_mod_cast Composition.dabs_nonneg (G := Hc.G) x v
    have hx0 : (0 : ℝ) ≤ ActiveCover.norm1 Hc.G x := by
      exact_mod_cast Composition.norm1_nonneg (G := Hc.G) x
    positivity


/-- Original certificate interface, preserved as a projection of the same core. -/
theorem native_congestion_of_H3H4 (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ L : ℝ, 0 < L ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∃ A : Finset V, (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 4 ∧
          ∀ x : Sym2 (Survivors A) → ℤ, x ∈ lattice (restrictedHost H A) F →
            ∃ cert : Finset (Survivors A) → ℤ,
              Dispersal.IsCert (restrictedHost H A).G (restrictedHost H A).lab F cert x ∧
              (Dispersal.l1T cert : ℝ) ≤ L * ActiveCover.norm1 (restrictedHost H A).G x ∧
              ∀ v, (Dispersal.vload cert v : ℝ) ≤ L *
                (ActiveCover.dabs (restrictedHost H A).G x v +
                  ActiveCover.norm1 (restrictedHost H A).G x / Fintype.card (Survivors A) + 1) := by
  obtain ⟨L, hL, n₀, hmain⟩ := native_congestion_with_geometry_of_H3H4 α h hα
  refine ⟨L, hL, n₀, ?_⟩
  intro V I _ H F hn hH3 hH4
  obtain ⟨A, hA, _hA3, _hA4, hcert⟩ := hmain H F hn hH3 hH4
  exact ⟨A, hA, hcert⟩

end TypedTriangle
