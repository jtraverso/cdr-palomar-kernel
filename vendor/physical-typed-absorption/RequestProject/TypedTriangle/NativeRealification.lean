/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeCongestion
public import RequestProject.S10.PhysicalAdapter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Bridge the native signed congestion theorem to the finite-matrix realification.
The core is chosen before any demand. This gives real certificates with homogeneous
L1 and vertex-load bounds; it does not assert the unconstructed smoothing kernel. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle
namespace NativeReal

open S10V22 ActiveCover Dispersal TypedTriangle.Composition
variable {V I : Type*} [Fintype V]

lemma cast_l1T (c : Finset V → ℤ) :
    S10V22.l1 (castV c) = (Dispersal.l1T c : ℝ) := by
  simp [S10V22.l1, castV, Dispersal.l1T]

lemma cast_norm1 (G : SimpleGraph V) (y : Sym2 V → ℤ)
    (hs : Composition.EdgeSupp G y) :
    S10V22.l1 (castV y) = (ActiveCover.norm1 G y : ℝ) := by
  rw [← Composition.l1E_eq_norm1 hs]
  simp [S10V22.l1, castV, Dispersal.l1E]

lemma cast_vload {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {c : Finset V → ℤ} {y : Sym2 V → ℤ} (hc : Dispersal.IsCert G lab F c y) (v : V) :
    load (triTw (allowedTri G lab F)) v (castV c) = (Dispersal.vload c v : ℝ) := by
  simp only [load, triTw, castV, Dispersal.vload, Int.cast_sum, Int.cast_abs,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hcT : c T = 0
  · simp [hcT]
  · have hT := mem_allowedTri.mpr (hc.1 T hcT)
    by_cases hv : v ∈ T <;> simp [hT, hv]

lemma cast_dabs (G : SimpleGraph V) (y : Sym2 V → ℤ)
    (hs : Composition.EdgeSupp G y) (v : V) :
    inLoad edgeEw v (castV y) = (ActiveCover.dabs G y v : ℝ) := by
  have heq : ActiveCover.dabs G y v =
      ∑ e ∈ SparseEdge.edges G, if v ∈ e then |y e| else 0 := by
    unfold ActiveCover.dabs
    symm
    exact Finset.sum_subtype _ (fun e => by simp [SparseEdge.edges])
      (fun e => if v ∈ e then |y e| else 0)
  rw [heq]
  simp only [inLoad, edgeEw, castV, Int.cast_sum, Int.cast_ite, Int.cast_abs,
    Int.cast_zero, SparseEdge.edges, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ∈ SparseEdge.edges G
  · have hnd : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet (SparseEdge.mem_edges.mp he)
    by_cases hv : v ∈ e <;> simp [SparseEdge.mem_edges.mp he, hnd, hv]
  · simp [he, hs e he]

lemma matrix_boundary {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {c : Finset V → ℤ} {y : Sym2 V → ℤ} (hc : Dispersal.IsCert G lab F c y) :
    intOp (triMat (allowedTri G lab F)) c = y := by
  rw [← hc.2]
  funext e
  simp only [intOp, triMat, Dispersal.triBd, SparseEdge.ind]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hcT : c T = 0
  · simp [hcT]
  · have hT := mem_allowedTri.mpr (hc.1 T hcT)
    rw [← triEdges_eq_edgesOf T]
    simp [hT, mul_comm]

/-- The native integer congestion contract supplies V22's exact matrix provider. -/
theorem provider_of_native {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {K : ℝ} (hcert : ∀ y ∈ TypedTriangle.lattice (⟨G,lab⟩ : Host V I) F,
      ∃ c : Finset V → ℤ, Dispersal.IsCert G lab F c y ∧
        (Dispersal.l1T c : ℝ) ≤ K * ActiveCover.norm1 G y ∧
        ∀ v, (Dispersal.vload c v : ℝ) ≤ K *
          (ActiveCover.dabs G y v + ActiveCover.norm1 G y / Fintype.card V + 1)) :
    IntCertProvider (triMat (allowedTri G lab F)) (triTw (allowedTri G lab F))
      edgeEw K (Fintype.card V : ℝ) := by
  intro y hy
  have hlat : y ∈ SparseEdge.lattice G lab F :=
    (mem_lattice_iff_intImage G lab F y).mpr hy
  obtain ⟨c, hc, hn, hv⟩ := hcert y hlat
  have hs := Composition.edgeSupp_of_lattice hlat
  refine ⟨c, matrix_boundary hc, ?_, fun v => ?_⟩
  · simpa only [cast_l1T, cast_norm1 G y hs] using hn
  · simpa only [cast_vload hc, cast_norm1 G y hs, cast_dabs G y hs] using hv v

end NativeReal
namespace NativeReal
open S10V22 ActiveCover

/-- Homogeneous real certificates on a uniformly chosen native core.
Only H3--H4 are inputs; neither an integer nor a real certificate provider is assumed.
The demand must lie in the actual real physical image. No integer or linear choice
of the resulting real certificates is asserted. -/
theorem realification_with_geometry_of_H3H4 (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∃ A : Finset V, (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 4 ∧
          CommonNbrCond (restrictedHost H A) F (α / 2) ∧
          HingeCond (restrictedHost H A) F (α / 2) h ∧
          letI : DecidableEq (Survivors A) := Classical.decEq (Survivors A)
          ∀ x : Sym2 (Survivors A) → ℝ,
            x ∈ realImage (triMat (allowedTri (restrictedHost H A).G
              (restrictedHost H A).lab F)) →
            RealCert (triMat (allowedTri (restrictedHost H A).G
              (restrictedHost H A).lab F))
              (triTw (allowedTri (restrictedHost H A).G (restrictedHost H A).lab F))
              edgeEw K (Fintype.card (Survivors A) : ℝ) x := by
  obtain ⟨K, hK, n₀, hnative⟩ := native_congestion_with_geometry_of_H3H4 α h hα
  refine ⟨K, hK, n₀, ?_⟩
  intro V I _ H F hn hH3 hH4
  classical
  obtain ⟨A, hA, hA3, hA4, hcert⟩ := hnative H F hn hH3 hH4
  letI : DecidableEq (Survivors A) := Classical.decEq (Survivors A)
  let Hc := restrictedHost H A
  have hp : IntCertProvider (triMat (allowedTri Hc.G Hc.lab F))
      (triTw (allowedTri Hc.G Hc.lab F)) edgeEw K (Fintype.card (Survivors A) : ℝ) :=
    provider_of_native (V := Survivors A) (I := I) (G := Hc.G)
      (lab := Hc.lab) (F := F) (K := K) hcert
  refine ⟨A, hA, hA3, hA4, ?_⟩
  intro x hx
  exact realCert_of_realImage hp hx


/-- Original realification interface, preserved as a projection. -/
theorem realification_of_H3H4 (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∃ A : Finset V, (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 4 ∧
          letI : DecidableEq (Survivors A) := Classical.decEq (Survivors A)
          ∀ x : Sym2 (Survivors A) → ℝ,
            x ∈ realImage (triMat (allowedTri (restrictedHost H A).G
              (restrictedHost H A).lab F)) →
            RealCert (triMat (allowedTri (restrictedHost H A).G
              (restrictedHost H A).lab F))
              (triTw (allowedTri (restrictedHost H A).G (restrictedHost H A).lab F))
              edgeEw K (Fintype.card (Survivors A) : ℝ) x := by
  obtain ⟨K, hK, n₀, hmain⟩ := realification_with_geometry_of_H3H4 α h hα
  refine ⟨K, hK, n₀, ?_⟩
  intro V I _ H F hn hH3 hH4
  obtain ⟨A, hA, _hA3, _hA4, hreal⟩ := hmain H F hn hH3 hH4
  exact ⟨A, hA, hreal⟩

end NativeReal
end TypedTriangle
