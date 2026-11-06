/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexRelativePaidReferenceExactSeed
public import RequestProject.TypedTriangle.VortexCleanHingeGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex

/-- Exactification on the same paid child retains the fixed clean hinge
order of the naked parent. The internal inverse certificate is supplied by
the scheduled producer; its auxiliary hinge order is not exported. -/
theorem relative_paid_child_with_clean_geometry
    (α β K ηSpec C η ζ ξ : ℝ) (h Nbase Ns nPaid nGeometry : ℕ)
    (hC : 1 ≤ C) (hη : 0 ≤ η) (hηQuarter : η ≤ 1 / 4)
    (hζ : 0 ≤ ζ) (hζSpec : ζ ≤ ηSpec) (hξ : 0 ≤ ξ)
    (hCap : PaidReferenceCap α h ηSpec nGeometry)
    (hspec : PaidSmoothAt α β K ηSpec h Nbase Ns nPaid)
    {V I : Type} [Fintype V] (J : Host V I)
    (F : Set (Multiset I)) (μ : Finset V → ℝ)
    (hn : max 1 (max nPaid nGeometry) ≤ Fintype.card V)
    (P : Dispersal.PreparedCore J.G J.lab F α h (max Nbase Ns) β)
    (h3 : CommonNbrCond J F α) (hClean : CleanHingeCond J F α h)
    (hμ : ∀ T, IsAllowed J F T →
      ((1 - η) / C) / Fintype.card V ≤ μ T ∧
        μ T ≤ ((1 + η) * C) / Fintype.card V)
    (hLoad : ∀ e ∈ edges J, |bdry J F μ e - 1| ≤ ξ)
    (E Y : Finset (Sym2 V)) (D : Finset (Finset V))
    (hD : IsDecomposition J F E D) (hY : Y ⊆ edges J)
    (hYPhys : IsPhysical J F Y) (hDis : Disjoint E Y)
    (hHole : ∀ v, (SparseEdge.degIn (edges J \ E) v : ℝ) ≤ ζ * Fintype.card V)
    (hζClean : ζ ≤ α / (10 * (2 : ℝ) ^ h.choose 2))
    (hBudget : K * (ξ + 2 * ((1 + η) * C) * ⌊ζ * Fintype.card V⌋₊ /
      Fintype.card V) ≤ η / C) :
    let Jchild := subHost J (E ∪ Y)
    ∃ ψ : Finset V → ℝ,
      IsDiffuseSeed Jchild F ((1 + 4 * η) * C) ψ ∧
      (∀ T, |ψ T - μ T| ≤ K *
        (ξ + 2 * ((1 + η) * C) * ⌊ζ * Fintype.card V⌋₊ /
          Fintype.card V) / Fintype.card V) ∧
      IsPhysical Jchild F (edges Jchild) ∧
      CommonNbrCond Jchild F (α / 2) ∧
      CleanHingeCond Jchild F (α / 2) h := by
  dsimp only
  obtain ⟨ψ, hψ, hClose, hPhysical, _, _⟩ :=
    paid_reference_relative_exact_seed_of_schedule α β K ηSpec C η ζ ξ
      h Nbase Ns nPaid nGeometry hC hη hηQuarter hζ hζSpec hξ hCap hspec
      J F μ hn P h3 hClean.hingeCond hμ hLoad E Y D hD hY hYPhys hDis hHole hBudget
  have hE : E ⊆ edges J := by
    intro e he
    obtain ⟨T,hT,heT⟩ := hD.exists_mem he
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
  have hCoefficient : 5 * ζ * (2 : ℝ) ^ h.choose 2 ≤ α / 2 := by
    have hScaled := (le_div_iff₀ (by positivity : (0 : ℝ) < 10 * 2 ^ h.choose 2)).mp hζClean
    nlinarith
  have hLoss : 5 * (d : ℝ) * 2 ^ h.choose 2 ≤ (α / 2) * Fintype.card V := by
    calc
      5 * (d : ℝ) * 2 ^ h.choose 2 ≤
          5 * (ζ * Fintype.card V) * 2 ^ h.choose 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) (by positivity)
      _ = (5 * ζ * 2 ^ h.choose 2) * Fintype.card V := by ring
      _ ≤ (α / 2) * Fintype.card V :=
        mul_le_mul_of_nonneg_right hCoefficient (by positivity)
  have hGeometry := clean_geometry_after_sparse_payment J F α (α / 2) h B d
    h3 hClean hBsub hBDeg hLoss
  rw [hRecover] at hGeometry
  have hGeometry' : CommonNbrCond (subHost J Echild) F (α / 2) ∧
      CleanHingeCond (subHost J Echild) F (α / 2) h := by
    simpa only [show α - α / 2 = α / 2 by ring] using hGeometry
  exact ⟨ψ,hψ,hClose,hPhysical,hGeometry'.1,hGeometry'.2⟩

#print axioms relative_paid_child_with_clean_geometry
end TypedTriangle.Vortex
