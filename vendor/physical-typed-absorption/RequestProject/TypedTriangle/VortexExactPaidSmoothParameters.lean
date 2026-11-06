/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexScheduledPaidSmoothCore
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

/-- A genuine, uniformly chosen hole window for physicality and geometry
of the reference-plus-paid-mode child. -/
def PaidReferenceCap (α : ℝ) (h : ℕ) (η : ℝ) (n₀ : ℕ) : Prop :=
  ∀ {V I : Type} [Fintype V] (J : Host V I) (F : Set (Multiset I)),
    n₀ ≤ Fintype.card V → CommonNbrCond J F α → HingeCond J F α h →
    ∀ (E Y : Finset (Sym2 V)) (D : Finset (Finset V)),
      IsDecomposition J F E D → Y ⊆ edges J → IsPhysical J F Y →
      Disjoint E Y →
      (∀ v, (SparseEdge.degIn (edges J \ E) v : ℝ) ≤ η * Fintype.card V) →
      let K := subHost J (E ∪ Y)
      IsPhysical K F (edges K) ∧
      CommonNbrCond K F (min (α / 2) (S07V49.hingeConstB α 1 h)) ∧
      HingeCond K F (min (α / 2) (S07V49.hingeConstB α 1 h)) (2 * h - 3)

theorem PaidReferenceCap.mono_budget {α η η' : ℝ} {h n₀ : ℕ}
    (P : PaidReferenceCap α h η n₀) (hle : η' ≤ η) :
    PaidReferenceCap α h η' n₀ := by
  intro V I _ J F hn h3 h4 E Y D hD hY hYPhys hDis hHole
  exact P J F hn h3 h4 E Y D hD hY hYPhys hDis (by
    intro v
    exact (hHole v).trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)))

theorem exists_paid_reference_cap (α : ℝ) (h : ℕ) (hα : 0 < α) (hh : 6 ≤ h) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ, PaidReferenceCap α h η n₀ := by
  obtain ⟨ηG, hηG, nG, hGeom⟩ := geometry_after_edge_payment_uniform α h hα hh
  obtain ⟨ηH, hηH, nH, hH2⟩ := intrinsic_H2_after_paid_mode α h hα
  let η := min ηG ηH
  refine ⟨η, lt_min hηG hηH, max nG nH, ?_⟩
  intro V I _ J F hn h3 h4 E Y D hD hY hYPhys hDis hHole
  dsimp only
  have hE : E ⊆ edges J := by
    intro e he
    obtain ⟨T, hT, heT⟩ := hD.exists_mem he
    exact triEdges_subset_edges (hD.1 T hT) heT
  let Echild := E ∪ Y
  let B := edges J \ Echild
  let d := ⌊η * Fintype.card V⌋₊
  have hEchild : Echild ⊆ edges J := union_subset hE hY
  have hBsub : B ⊆ edges J := sdiff_subset
  have hBhole : B ⊆ edges J \ E := by
    intro e he
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,
      fun hc => (mem_sdiff.mp he).2 (mem_union_left _ hc)⟩
  have hBReal : ∀ v, (SparseEdge.degIn B v : ℝ) ≤ η * Fintype.card V := by
    intro v
    have hc := card_le_card (filter_subset_filter (p := fun e => v ∈ e) hBhole)
    have hc' : (SparseEdge.degIn B v : ℝ) ≤ SparseEdge.degIn (edges J \ E) v := by
      exact_mod_cast hc
    exact hc'.trans (hHole v)
  have hBDeg : ∀ v, SparseEdge.degIn B v ≤ d := fun v => Nat.le_floor (hBReal v)
  have hd : (d : ℝ) ≤ η * Fintype.card V := Nat.floor_le (by
    have : 0 < η := lt_min hηG hηH
    positivity)
  have hRecover : edges J \ B = Echild := by
    dsimp only [B]
    ext e
    simp only [mem_sdiff]
    have he : e ∈ Echild → e ∈ edges J := fun hp => hEchild hp
    tauto
  have hGeometry := hGeom J F B d ((le_max_left _ _).trans hn) h3 h4 hBsub hBDeg
    (hd.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)))
  rw [hRecover] at hGeometry
  have hPhys : IsPhysical (subHost J Echild) F (edges (subHost J Echild)) :=
    hH2 J F ((le_max_right _ _).trans hn) h3 h4 E Y hE hY
      (isPhysical_of_isDecomposition hD) hYPhys hDis (by
        intro v
        have hb := (hHole v).trans
          (mul_le_mul_of_nonneg_right (min_le_right ηG ηH) (Nat.cast_nonneg _))
        simpa only [SparseEdge.degIn, TypedTriangle.degIn] using hb)
  exact ⟨hPhys, commonNbrCond_mono hGeometry.1 (min_le_left _ _),
    hingeCond_mono hGeometry.2 (min_le_right _ _)⟩

theorem paidSmoothAt_mono_budget {α β K η η' : ℝ} {h Nb Ns Np : ℕ}
    (P : PaidSmoothAt α β K η h Nb Ns Np) (hle : η' ≤ η) :
    PaidSmoothAt α β K η' h Nb Ns Np := by
  intro V I _ J F hn Pc h3 h4 B d hBE hDeg hSmall
  exact P J F hn Pc h3 h4 B d hBE hDeg
    (hSmall.trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)))

theorem paidSmoothAt_mono_constant {α β K K' η : ℝ} {h Nb Ns Np : ℕ}
    (P : PaidSmoothAt α β K η h Nb Ns Np) (hle : K ≤ K') :
    PaidSmoothAt α β K' η h Nb Ns Np := by
  intro V I _ J F hn Pc h3 h4 B d hBE hDeg hSmall
  dsimp only
  intro h3Child h4Child
  have hSmooth := P J F hn Pc h3 h4 B d hBE hDeg hSmall h3Child h4Child
  intro x hx ε hε hxBound
  obtain ⟨w, hSupport, hBoundary, hBound⟩ := hSmooth x hx ε hε hxBound
  refine ⟨w, hSupport, hBoundary, ?_⟩
  intro T
  exact (hBound T).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hle hε) (Nat.cast_nonneg _))

/-- Choose the physical/geometric cap before the radius schedule, and
inflate its inverse constant to dominate the reciprocal of that cap. The
later exactification hole tolerance will be smaller, so no inverse/tolerance
fixed point is imposed. -/
theorem exists_exact_paid_smooth_constant_function (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h) :
    ∃ nGeometry : ℕ, ∃ K : ℝ → ℝ,
      (∀ β, 0 < β → 0 < K β) ∧
      ∀ β, 0 < β → ∃ ηMax : ℝ, 0 < ηMax ∧ 1 ≤ K β * ηMax ∧
        PaidReferenceCap α h ηMax nGeometry ∧
        ∃ Nbase Ns nPaid : ℕ,
          PaidSmoothAt α β (K β) ηMax h Nbase Ns nPaid := by
  obtain ⟨ηRef, hηRef, nGeometry, hRef⟩ := exists_paid_reference_cap α h hα hh
  obtain ⟨K₀, hK₀, hPaid⟩ := exists_paid_smooth_constant_function α h hα hh
  have hChoice : ∀ β : ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ Nb Ns Np : ℕ,
      0 < β → PaidSmoothAt α β (K₀ β) η₀ h Nb Ns Np := by
    intro β
    by_cases hβ : 0 < β
    · obtain ⟨η₀, hη₀, Nb, Ns, Np, hSpec⟩ := hPaid β hβ
      exact ⟨η₀, hη₀, Nb, Ns, Np, fun _ => hSpec⟩
    · exact ⟨1, by norm_num, 0, 0, 0, fun hp => False.elim (hβ hp)⟩
  choose η₀ hη₀ Nb Ns Np hSpec using hChoice
  let ηMax : ℝ → ℝ := fun β => min (η₀ β) ηRef
  have hηMax : ∀ β, 0 < ηMax β := fun β => lt_min (hη₀ β) hηRef
  let K : ℝ → ℝ := fun β => max (K₀ β) (1 / ηMax β)
  refine ⟨nGeometry, K, ?_, ?_⟩
  · intro β _
    exact lt_of_lt_of_le (div_pos (by norm_num) (hηMax β)) (le_max_right _ _)
  intro β hβ
  have hDominates : 1 ≤ K β * ηMax β := by
    have hb := mul_le_mul_of_nonneg_right (le_max_right (K₀ β) (1 / ηMax β)) (hηMax β).le
    have hid : (1 / ηMax β) * ηMax β = 1 := div_mul_cancel₀ 1 (hηMax β).ne'
    rw [hid] at hb
    exact hb
  refine ⟨ηMax β, hηMax β, hDominates,
    hRef.mono_budget (min_le_right _ _), Nb β, Ns β, Np β, ?_⟩
  exact paidSmoothAt_mono_constant
    (paidSmoothAt_mono_budget (hSpec β hβ) (min_le_left _ _)) (le_max_left _ _)

#print axioms exists_paid_reference_cap
#print axioms paidSmoothAt_mono_budget
#print axioms paidSmoothAt_mono_constant
#print axioms exists_exact_paid_smooth_constant_function

end TypedTriangle.Vortex
