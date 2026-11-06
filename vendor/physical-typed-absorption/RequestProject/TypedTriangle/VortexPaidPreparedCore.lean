/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexPaidLatticePersist
public import RequestProject.TypedTriangle.VortexPaidChildGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Assemble geometry and lattice persistence on the actual paid child. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem paid_prepared_core_of_lattice {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I))
    (α β η : ℝ) (h N₀ nG d : ℕ)
    (P : Dispersal.PreparedCore H.G H.lab F α h N₀ β)
    (hβ : β ≤ 1 / 2) (hη : 0 < η) (hN : nG ≤ N₀)
    (hGeo : ∀ {U J : Type} [Fintype U] (R : Host U J)
      (F' : Set (Multiset J)) (B' : Finset (Sym2 U)) (d' : ℕ),
      nG ≤ Fintype.card U → CommonNbrCond R F' α → HingeCond R F' α h →
      B' ⊆ edges R → (∀ v, SparseEdge.degIn B' v ≤ d') →
      (d' : ℝ) ≤ η * Fintype.card U →
      CommonNbrCond (subHost R (edges R \ B')) F' (α / 2) ∧
      HingeCond (subHost R (edges R \ B')) F'
        (S07V49.hingeConstB α 1 h) (2*h-3))
    (B : Finset (Sym2 V)) (hBE : B ⊆ edges H)
    (hDeg : ∀ v, SparseEdge.degIn B v ≤ d)
    (hSmall : (d : ℝ) ≤ η / 2 * Fintype.card V)
    (hLat : ∀ Z : Finset V, (Z.card : ℝ) ≤ β * Fintype.card V →
      ∀ y ∈ lattice (subHost H (edges H \ B)) F,
        (∀ e : Sym2 V, (∃ z ∈ Z, z ∈ e) → y e = 0) →
          Dispersal.restr Z y ∈ lattice
            (restrictedHost (subHost H (edges H \ B)) Z) F) :
    Dispersal.PreparedCore
      (subHost H (edges H \ B)).G (subHost H (edges H \ B)).lab F
      (min (α / 2) (S07V49.hingeConstB α 1 h)) (2*h-3) N₀ β := by
  let J := subHost H (edges H \ B)
  have hG (Z : Finset V) (hZ : (Z.card : ℝ) ≤ β * Fintype.card V) :
      CommonNbrCond (restrictedHost J Z) F
        (min (α / 2) (S07V49.hingeConstB α 1 h)) ∧
      HingeCond (restrictedHost J Z) F
        (min (α / 2) (S07V49.hingeConstB α 1 h)) (2*h-3) := by
    have hcard : (Fintype.card (Survivors Z) : ℝ) + Z.card = Fintype.card V := by
      exact_mod_cast card_survivors_add_card Z
    have hn0 : (0 : ℝ) ≤ Fintype.card V := by positivity
    have hhalf : (Fintype.card V : ℝ) / 2 ≤ Fintype.card (Survivors Z) := by
      have hb := mul_le_mul_of_nonneg_right hβ hn0
      nlinarith
    have hload : (d : ℝ) ≤ η * Fintype.card (Survivors Z) := by
      have heta : 0 ≤ η := hη.le
      nlinarith [hSmall]
    have hB' : restrictEdgeSet Z B ⊆ edges (restrictedHost H Z) := by
      intro e he
      have heH := hBE ((mem_restrictEdgeSet Z B e).mp he)
      induction e using Sym2.ind with
      | _ u v =>
        have heG : H.G.Adj u.1 v.1 := by
          simpa only [Sym2.map_mk, edges, Finset.mem_filter, Finset.mem_univ,
            true_and, SimpleGraph.mem_edgeSet] using heH
        simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and]
        change H.G.Adj u.1 v.1
        exact heG
    have hD' : ∀ v : Survivors Z,
        SparseEdge.degIn (restrictEdgeSet Z B) v ≤ d := by
      intro v
      convert (restricted_edge_load_le Z B v).trans (hDeg v.1) using 1
      unfold SparseEdge.degIn
      congr 1
      apply Finset.ext
      intro e
      simp only [Finset.mem_filter]
    have h3raw : CommonNbrCond (restrictedHost H Z) F α := P.h3 Z hZ
    have h4raw : HingeCond (restrictedHost H Z) F α h := P.h4 Z hZ
    have hraw := hGeo (restrictedHost H Z) F (restrictEdgeSet Z B) d
      (hN.trans (P.order Z hZ)) h3raw h4raw
      hB' hD' hload
    have hHost : subHost (restrictedHost H Z)
        (edges (restrictedHost H Z) \ restrictEdgeSet Z B) =
        restrictedHost J Z := by
      convert (restricted_paid_child_eq_paid_restricted H Z B).symm using 1 <;>
        (congr 1 <;> apply Finset.ext <;> intro e <;> simp only [Finset.mem_sdiff])
    have hraw3' : CommonNbrCond
        (subHost (restrictedHost H Z)
          (edges (restrictedHost H Z) \ restrictEdgeSet Z B)) F (α/2) := by
      convert hraw.1 using 1 <;>
        (congr 1 <;> apply Finset.ext <;> intro e <;> simp only [Finset.mem_sdiff])
    have hpaid3 : CommonNbrCond (restrictedHost J Z) F (α/2) :=
      hHost ▸ hraw3'
    have hraw4' : HingeCond
        (subHost (restrictedHost H Z)
          (edges (restrictedHost H Z) \ restrictEdgeSet Z B)) F
        (S07V49.hingeConstB α 1 h) (2*h-3) := by
      convert hraw.2 using 1 <;>
        (congr 1 <;> apply Finset.ext <;> intro e <;> simp only [Finset.mem_sdiff])
    have hpaid4 : HingeCond (restrictedHost J Z) F
        (S07V49.hingeConstB α 1 h) (2*h-3) :=
      hHost ▸ hraw4'
    exact ⟨commonNbrCond_mono hpaid3 (min_le_left _ _),
      hingeCond_mono hpaid4 (min_le_right _ _)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z hZ
    exact (hG Z hZ).1
  · intro Z hZ
    exact (hG Z hZ).2
  · intro Z hZ
    exact P.order Z hZ
  · intro Z hZ y hy hvan
    exact hLat Z hZ y hy hvan

#print axioms paid_prepared_core_of_lattice

/-- A single uniform degree budget preserves the prepared core on the paid
child. The order threshold and degree margin are chosen before the host. -/
theorem paid_prepared_core_uniform (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (β : ℝ),
        0 < β → β ≤ 1/2 →
        Dispersal.PreparedCore H.G H.lab F α h N₀ β →
        CommonNbrCond H F α → HingeCond H F α h →
        ∀ (B : Finset (Sym2 V)) (d : ℕ), B ⊆ edges H →
          (∀ v, SparseEdge.degIn B v ≤ d) →
          (d : ℝ) ≤ η * Fintype.card V →
          Dispersal.PreparedCore
            (subHost H (edges H \ B)).G (subHost H (edges H \ B)).lab F
            (min (α/2) (S07V49.hingeConstB α 1 h)) (2*h-3) N₀ β := by
  obtain ⟨ηG,hηG,nG,hGeo⟩ := geometry_after_edge_payment_uniform α h hα hh
  obtain ⟨ηL,hηL,nL,hLat⟩ := paid_lattice_persist_after_sparse_edge_deletion α h hα
  refine ⟨min (ηG/2) (ηL/2), lt_min (by positivity) (by positivity),
    max nG nL, ?_⟩
  intro V I _ H F β hβ hβhalf P hRaw3 hRaw4 B d hBE hDeg hSmall
  have hN : nG ≤ max nG nL := le_max_left _ _
  have hnL : nL ≤ Fintype.card V := by
    have hzero : (0 : ℝ) ≤ β * Fintype.card V := by positivity
    have ho := P.order ∅ (by simpa using hzero)
    have hcard : Fintype.card (Survivors (∅ : Finset V)) = Fintype.card V := by
      have hc := card_survivors_add_card (∅ : Finset V)
      simpa using hc
    exact (le_max_right _ _).trans (hcard ▸ ho)
  let Psmall : Dispersal.PreparedCore H.G H.lab F α h nL β :=
    { h3 := P.h3, h4 := P.h4,
      order := fun Z hZ => (le_max_right _ _).trans (P.order Z hZ),
      lattice_persist := P.lattice_persist }
  have hn0 : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hGsmall : (d : ℝ) ≤ ηG / 2 * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
  have hLsmall : (d : ℝ) ≤ ηL / 2 * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0)
  have hB : ∀ x, (((B.filter (fun e => x ∈ e)).card : ℕ) : ℝ) ≤
      ηL / 2 * Fintype.card V := by
    intro x
    have hDx := hDeg x
    have hC : ((B.filter (fun e => x ∈ e)).card : ℝ) ≤ d := by
      unfold SparseEdge.degIn at hDx
      exact_mod_cast hDx
    exact hC.trans hLsmall
  have hPersist := hLat V I H F β hβhalf hnL hRaw3 hRaw4 Psmall B hB
  exact paid_prepared_core_of_lattice H F α β ηG h (max nG nL) nG d
    P hβhalf hηG hN hGeo B hBE hDeg hGsmall hPersist

#print axioms paid_prepared_core_uniform

end TypedTriangle.Vortex
