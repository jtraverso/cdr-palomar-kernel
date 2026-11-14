/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.PaperIII.Defs
public import CDRBicolour.KBicolor.Four

/-!
# Bridge: an allowed decomposition of the `k`-class host is a `k`-bicolourable STS
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.PaperIII

open Finset TypedTriangle CDRBicolour.KBicolor

/-- An allowed decomposition of all edges of the complete host labelled by `lab`, with all
classes nonempty, is an STS with a bicolouring by exactly `k` colours. -/
theorem bicolourable_of_decomposition {v k : ℕ} (lab : Fin v → Fin k)
    (hpos : ∀ X, 0 < ksz lab X) (D : Finset (Finset (Fin v)))
    (hD : IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D) : Bicolourable v k := by
  classical
  obtain ⟨hall, hdisj, hcov⟩ := hD
  have hmem : ∀ T ∈ D, ∀ x y, x ≠ y → (s(x, y) ∈ triEdges T ↔ x ∈ T ∧ y ∈ T) := by
    intro T _ x y hxy
    simp [triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff, hxy]
  refine ⟨D, lab, ⟨fun T hT => (hall T hT).1, fun x y hxy => ?_⟩, ⟨fun X => ?_, fun T hT => ?_⟩⟩
  · have he : s(x, y) ∈ edges (kHost lab) := by simp [edges, kHost, hxy]
    rw [← hcov] at he
    simp only [Finset.mem_biUnion] at he
    obtain ⟨T, hT, hxyT⟩ := he
    refine ⟨T, ⟨hT, (hmem T hT x y hxy).1 hxyT⟩, ?_⟩
    rintro T' ⟨hT', hx', hy'⟩
    by_contra hne
    have := hdisj hT' hT hne
    exact disjoint_left.1 this ((hmem T' hT' x y hxy).2 ⟨hx', hy'⟩) hxyT
  · have h := hpos X
    unfold ksz at h
    obtain ⟨x, hx⟩ := card_pos.1 h
    exact ⟨x, (mem_filter.1 hx).2⟩
  · have h := (hall T hT).2.2
    show ((T.val.map lab).toFinset).card = 2
    exact h.2

end CDRBicolour.PaperIII
