/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SampleConstruct
public import RequestProject.TypedTriangle.CertDispersal
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Local adapter candidate: derive V15's certificate interface from the actual
canonical theorem, with zero extension of coefficients outside allowed triangles.
Pending the local rc3 audit. No avoiding-certificate provider is assumed. -/

open Finset Classical

noncomputable section

namespace TypedTriangle

open Incidence

variable {V I : Type*} [Fintype V]

lemma native_triBd_eq_of_allowed_support (H : Host V I) (F : Set (Multiset I))
    (c : Finset V → ℤ) (hsupp : ∀ T, ¬ IsAllowed H F T → c T = 0) :
    Dispersal.triBd c = triBd H F c := by
  funext e
  rw [triBd_apply]
  change (∑ T, c T * ind (triEdges T) e) =
    ∑ T ∈ allowed H F, c T * ind (triEdges T) e
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro T _ hT
  have hnot : ¬ IsAllowed H F T := by
    intro h
    exact hT (Finset.mem_filter.mpr ⟨Finset.mem_univ T, h⟩)
  rw [hsupp T hnot, zero_mul]

/-- UniformCertOn is a consequence, rather than a new hypothesis, at universe zero.
The original canonical theorem quantifies over V,I : Type; this preserves that scope. -/
theorem native_uniformCertOn_of_H3H4 (α : ℝ) (h k : ℕ) (hα : 0 < α) :
    ∃ K n₀ : ℕ, ∀ {I : Type} (F : Set (Multiset I)),
      Dispersal.UniformCertOn.{0} F α h n₀ k K := by
  obtain ⟨K₀, n₀, hcert⟩ := uniformCert_of_H3H4 α h hα
  refine ⟨K₀ * k, n₀, ?_⟩
  intro I F W _ G lab hH3 hH4 hn y hy hk
  obtain ⟨c, hc, hcost⟩ := hcert (⟨G, lab⟩ : Host W I) F hn hH3 hH4 y hy
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

end TypedTriangle
