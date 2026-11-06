/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SmoothExactification
public import RequestProject.TypedTriangle.SampledRawWeights
public import RequestProject.S10.PhysicalAdapter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Exact H1 on a predetermined sampled host. The real-image and smooth
inverse premises refer to that very host, not to a newly selected subcore. -/

open Finset Classical S10V22
noncomputable section

namespace TypedTriangle.Vortex

variable {V I : Type*} [Fintype V] [DecidableEq V]

private theorem realOp_eq_bdry (H : Host V I) (F : Set (Multiset I))
    (μ : Finset V → ℝ) (e : Sym2 V) :
    realOp (triMat (allowedTri H.G H.lab F)) μ e = bdry H F μ e := by
  have hsets : allowedTri H.G H.lab F = allowed H F := by
    ext T
    rw [S10V22.mem_allowedTri]
    simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hsets]
  simp only [realOp_apply, bdry]
  change (∑ T ∈ (univ : Finset (Finset V)),
      (triMat (allowed H F) e T : ℝ) * μ T) =
    ∑ T ∈ (univ : Finset (Finset V)).filter (IsAllowed H F),
      μ T * indR (triEdges T) e
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hA : IsAllowed H F T
  · have hA' : T ∈ allowed H F := by simpa [allowed] using hA
    simp [triMat, hA', hA, indR, S10V22.edgesOf, triEdges, mul_comm]
  · have hA' : T ∉ allowed H F := by simpa [allowed] using hA
    simp [triMat, hA', hA]

/-- A physical target and a smooth inverse exactify approximate loads on the
same fixed host with an explicit decidable equality. This does not assert that the smooth inverse follows from
the original H1--H4 on an arbitrary predetermined sample. -/
theorem exact_seed_on_fixed_host_of_smooth_explicit (J : Host V I) (F : Set (Multiset I))
    (C K ξ : ℝ) (hC : 1 ≤ C) (hξ : 0 ≤ ξ)
    (hS : NativeSmooth.Smooth J F K)
    (hPhysical : IsPhysical J F (edges J))
    (μ : Finset V → ℝ)
    (hμsupp : ∀ T, μ T ≠ 0 → IsAllowed J F T)
    (hμ : ∀ T, IsAllowed J F T →
      (1 / (2*C)) / Fintype.card V ≤ μ T ∧
        μ T ≤ (2*C) / Fintype.card V)
    (hload : ∀ e ∈ edges J, |bdry J F μ e - 1| ≤ ξ)
    (hbudget : K * ξ ≤ 1 / (4*C)) :
    ∃ ψ : Finset V → ℝ, IsDiffuseSeed J F (4*C) ψ := by
  let b : Sym2 V → ℝ := castV (ind (edges J))
  have hb : b ∈ realImage (triMat (allowedTri J.G J.lab F)) := by
    exact S10V22.castV_mem_realImage_of_lattice
      (G := J.G) (lab := J.lab) (F := F) hPhysical
  have hdef : ∀ e,
      |(b - realOp (triMat (allowedTri J.G J.lab F)) μ) e| ≤ ξ := by
    intro e
    by_cases he : e ∈ edges J
    · have := hload e he
      simpa [b, castV, ind, he, Pi.sub_apply, realOp_eq_bdry,
        abs_sub_comm] using this
    · have hz : bdry J F μ e = 0 := bdry_eq_zero_of_not_mem J F μ he
      simp [b, castV, ind, he, Pi.sub_apply, realOp_eq_bdry, hz, hξ]
  obtain ⟨ψ, _, hψload, _, hψbounds⟩ :=
    NativeSmooth.exactify_of_smooth J F hS μ b hb hμsupp hξ hμ hdef
      (by convert hbudget using 1 <;> ring)
  refine ⟨ψ, ?_, ?_⟩
  · intro T hT
    have hh := hψbounds T hT
    constructor
    · convert hh.1 using 1 <;> ring
    · have hpos : (0 : ℝ) < C := by linarith
      have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
      have hc : 2*C + (1 / (2*C)) / 2 ≤ 4*C := by
        have hfrac : 1 / (4*C) ≤ (1:ℝ) := by
          apply (div_le_iff₀ (by positivity : (0:ℝ) < 4*C)).mpr
          nlinarith
        have hfrac' : (1 / (2*C*2) : ℝ) ≤ 1 := by
          convert hfrac using 1 <;> ring
        rw [div_div]
        nlinarith [hfrac']
      exact hh.2.trans (div_le_div_of_nonneg_right hc hn)
  · intro e he
    have he' : e ∈ edges J := by simpa [edges] using he
    have hvalue := congrFun hψload e
    change (∑ T ∈ triOn J F e, ψ T) = 1
    rw [← bdry_eq_sum_triOn]
    simpa [b, castV, ind, he', realOp_eq_bdry] using hvalue

#print axioms exact_seed_on_fixed_host_of_smooth_explicit

end TypedTriangle.Vortex
