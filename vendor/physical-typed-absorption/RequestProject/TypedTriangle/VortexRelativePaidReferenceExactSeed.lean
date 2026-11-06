/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexExactPaidSmoothParameters
public import RequestProject.TypedTriangle.VortexRelativeExactSeed
public import RequestProject.TypedTriangle.VortexPaidSameSampleExactSeed
public import RequestProject.TypedTriangle.VortexPaidChildGeometry
public import RequestProject.TypedTriangle.G4IntrinsicDensePaidMode
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex
open CatalogNative

/-- Re-anchor exact H1 at a raw profile of the naked host. Sparse paid holes
only enter the boundary error; the correction remains globally close to the
same raw profile, with no recurrence through a previous exact seed. -/
theorem paid_reference_relative_exact_seed_of_schedule
    (α β K ηSpec C η ζ ξ : ℝ) (h Nbase Ns nPaid nGeometry : ℕ)
    (hC : 1 ≤ C) (hη : 0 ≤ η) (hηQuarter : η ≤ 1 / 4)
    (hζ : 0 ≤ ζ) (hζSpec : ζ ≤ ηSpec) (hξ : 0 ≤ ξ)
    (hCap : PaidReferenceCap α h ηSpec nGeometry)
    (hspec : PaidSmoothAt α β K ηSpec h Nbase Ns nPaid)
    {V I : Type} [Fintype V] (J : Host V I)
    (F : Set (Multiset I)) (μ : Finset V → ℝ)
    (hn : max 1 (max nPaid nGeometry) ≤ Fintype.card V)
    (P : Dispersal.PreparedCore J.G J.lab F α h (max Nbase Ns) β)
    (h3 : CommonNbrCond J F α) (h4 : HingeCond J F α h)
    (hμ : ∀ T, IsAllowed J F T →
      ((1 - η) / C) / Fintype.card V ≤ μ T ∧
        μ T ≤ ((1 + η) * C) / Fintype.card V)
    (hLoad : ∀ e ∈ edges J, |bdry J F μ e - 1| ≤ ξ)
    (E Y : Finset (Sym2 V)) (D : Finset (Finset V))
    (hD : IsDecomposition J F E D) (hY : Y ⊆ edges J)
    (hYPhys : IsPhysical J F Y) (hDis : Disjoint E Y)
    (hHole : ∀ v, (SparseEdge.degIn (edges J \ E) v : ℝ) ≤ ζ * Fintype.card V)
    (hBudget : K * (ξ + 2 * ((1 + η) * C) * ⌊ζ * Fintype.card V⌋₊ /
      Fintype.card V) ≤ η / C) :
    let Jchild := subHost J (E ∪ Y)
    ∃ ψ : Finset V → ℝ,
      IsDiffuseSeed Jchild F ((1 + 4 * η) * C) ψ ∧
      (∀ T, |ψ T - μ T| ≤ K *
        (ξ + 2 * ((1 + η) * C) * ⌊ζ * Fintype.card V⌋₊ /
          Fintype.card V) / Fintype.card V) ∧
      IsPhysical Jchild F (edges Jchild) ∧
      CommonNbrCond Jchild F (min (α / 2) (S07V49.hingeConstB α 1 h)) ∧
      HingeCond Jchild F (min (α / 2) (S07V49.hingeConstB α 1 h)) (2 * h - 3) := by
  dsimp only
  have hn1 : 1 ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnPos : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn1
  have hnPaid : nPaid ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnGeom : nGeometry ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hE : E ⊆ edges J := by
    intro e he
    obtain ⟨T, hT, heT⟩ := hD.exists_mem he
    exact triEdges_subset_edges (hD.1 T hT) heT
  let Echild := E ∪ Y
  let B := edges J \ Echild
  let d := ⌊ζ * Fintype.card V⌋₊
  have hEchild : Echild ⊆ edges J := union_subset hE hY
  have hBsub : B ⊆ edges J := sdiff_subset
  have hBhole : B ⊆ edges J \ E := by
    intro e he
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,
      fun hc => (mem_sdiff.mp he).2 (mem_union_left _ hc)⟩
  have hBDegReal : ∀ v, (SparseEdge.degIn B v : ℝ) ≤ ζ * Fintype.card V := by
    intro v
    have hc := card_le_card (filter_subset_filter (p := fun e => v ∈ e) hBhole)
    have hc' : (SparseEdge.degIn B v : ℝ) ≤ SparseEdge.degIn (edges J \ E) v := by
      exact_mod_cast hc
    exact hc'.trans (hHole v)
  have hBDeg : ∀ v, SparseEdge.degIn B v ≤ d := fun v => Nat.le_floor (hBDegReal v)
  have hd : (d : ℝ) ≤ ζ * Fintype.card V := Nat.floor_le (by positivity)
  have hRecover : edges J \ B = Echild := by
    dsimp only [B]
    ext e
    simp only [mem_sdiff]
    have he : e ∈ Echild → e ∈ edges J := fun hp => hEchild hp
    tauto
  have hCapChild := (hCap.mono_budget hζSpec) J F hnGeom h3 h4 E Y D
    hD hY hYPhys hDis hHole
  have hPhysical : IsPhysical (subHost J Echild) F (edges (subHost J Echild)) :=
    hCapChild.1
  have hChild3 : CommonNbrCond (subHost J Echild) F
      (min (α / 2) (S07V49.hingeConstB α 1 h)) := hCapChild.2.1
  have hChild4 : HingeCond (subHost J Echild) F
      (min (α / 2) (S07V49.hingeConstB α 1 h)) (2 * h - 3) := hCapChild.2.2
  have hSmooth := hspec J F hnPaid P h3 h4 B d hBsub hBDeg
    (hd.trans (mul_le_mul_of_nonneg_right hζSpec (Nat.cast_nonneg _)))
  rw [hRecover] at hSmooth
  have hSmoothChild := hSmooth hChild3 hChild4
  have hNonneg : ∀ T, IsAllowed J F T →
      0 ≤ μ T ∧ μ T ≤ ((1 + η) * C) / Fintype.card V := by
    intro T hT
    refine ⟨?_, (hμ T hT).2⟩
    exact (div_nonneg (div_nonneg (by linarith) (by linarith)) hnPos.le).trans
      (hμ T hT).1
  have hRaw := RawReference.load_after_deletion μ B d ((1 + η) * C) ξ
    hnPos (by positivity) hNonneg
    (by intro v; simpa only [TypedTriangle.degIn, SparseEdge.degIn] using hBDeg v) hLoad
  have hResidual : residual J B = subHost J Echild := by
    dsimp only [residual]
    rw [hRecover]
  rw [hResidual] at hRaw
  have hWeights : ∀ T, IsAllowed (subHost J Echild) F T →
      ((1 - η) / C) / Fintype.card V ≤ μ T ∧
        μ T ≤ ((1 + η) * C) / Fintype.card V := by
    intro T hT
    exact hμ T (isAllowed_mono (subHost_le J Echild) rfl hT)
  obtain ⟨ψ, hψ, hClose⟩ := exact_seed_on_fixed_host_with_relative_loss
    (subHost J Echild) F C K (ξ + 2 * ((1 + η) * C) * d / Fintype.card V) η
    hC hη hηQuarter (by positivity) hSmoothChild hPhysical μ hWeights hRaw hBudget
  exact ⟨ψ, hψ, hClose, hPhysical, hChild3, hChild4⟩

#print axioms paid_reference_relative_exact_seed_of_schedule

end TypedTriangle.Vortex
