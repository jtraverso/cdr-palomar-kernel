/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitG1ZSplice
public import RequestProject.TypedTriangle.ExplicitUniformCompression
public import RequestProject.TypedTriangle.NativeUniformCertAdapter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
namespace TypedTriangle.ExplicitCertificate
open Incidence

def uniformCertCost (α : ℝ) (h : ℕ) : ℕ :=
  let s := ExplicitSample.compressionSampleSize α h
  compressionCertCost s (compH0 (min α 1) s) (compD0 (min α 1) s)

theorem uniformCertCost_pos (α : ℝ) (h : ℕ) : 1 ≤ uniformCertCost α h := by
  dsimp only [uniformCertCost, compressionCertCost, compH0]
  omega

theorem uniformCert_of_H3H4_explicit (α : ℝ) (h : ℕ) (hα : 0 < α)
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (hn : ExplicitSample.compressionOrder α h ≤ Fintype.card V)
    (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) :
    UniformCert H F (uniformCertCost α h) := by
  obtain ⟨cmp⟩ := ExplicitSample.compression_of_H3H4_explicit α h hα H F hn hH3 hH4
  exact g1z_of_compression_explicit _ _ _ H F cmp

theorem native_uniformCertOn_of_H3H4_explicit (α : ℝ) (h k : ℕ) (hα : 0 < α) :
    ∀ {I : Type} (F : Set (Multiset I)),
      Dispersal.UniformCertOn.{0} F α h (ExplicitSample.compressionOrder α h) k (uniformCertCost α h*k) := by
  let K₀ := uniformCertCost α h
  intro I F W _ G lab hH3 hH4 hn y hy hk
  obtain ⟨c, hc, hcost⟩ := uniformCert_of_H3H4_explicit α h hα (⟨G, lab⟩ : Host W I) F hn hH3 hH4 y hy
  let H : Host W I := ⟨G, lab⟩
  let d : Finset W → ℤ := fun T => if IsAllowed H F T then c T else 0
  have hsupp : ∀ T, ¬ IsAllowed H F T → d T = 0 := by
    intro T hT
    simp [d, hT]
  have hbd : Dispersal.triBd d = y := by
    rw [native_triBd_eq_of_allowed_support H F d hsupp, ← hc]
    change (∑ T ∈ allowed H F, d T • ind (triEdges T)) =
      ∑ T ∈ allowed H F, c T • ind (triEdges T)
    apply Finset.sum_congr rfl
    intro T hT
    have hallowed := (Finset.mem_filter.mp hT).2
    simp [d, hallowed]
  refine ⟨d, ⟨?_, hbd⟩, ?_⟩
  · intro T hT
    by_contra hnT
    exact hT (hsupp T hnT)
  · have hnorm : Dispersal.l1T d ≤ ∑ T, |c T| := by
      apply Finset.sum_le_sum
      intro T _
      by_cases hT : IsAllowed H F T
      · simp [d, hT]
      · simp [d, hT]
    have hcost' : (K₀ : ℤ) * l1E y ≤ ((K₀ * k : ℕ) : ℤ) := by
      push_cast
      exact mul_le_mul_of_nonneg_left hk (by positivity)
    exact hnorm.trans (hcost.trans hcost')

#print axioms uniformCertCost_pos
#print axioms uniformCert_of_H3H4_explicit
#print axioms native_uniformCertOn_of_H3H4_explicit
end TypedTriangle.ExplicitCertificate
