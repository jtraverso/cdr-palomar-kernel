/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.MainPaperIII
public import CDRBicolour.Absorption.ResidualHinge
public import CDRBicolour.Absorption.AACCount
public import CDRBicolour.Absorption.ResidualSeedCDR

/-!
# Completion of sparse bicoloured packings (backlog item 2a), conditional on residual H1

Let `P` be a packing of bicoloured triangles of the CDR host whose leave has maximum degree
`Δ ≤ n/64 - 1`.  The residual host `G = K_n - E(P)` satisfies H2 (`residual_physical`), H3
(`residual_H3`) and H4 (`residual_H4`) — all proved.  If moreover `G` has a diffuse seed (H1),
Theorem T decomposes `G`, and `P` together with that decomposition is a strictly bicoloured STS
with the prescribed classes containing `P` (`cdr_completion_of_seed`).

The residual seed is the only hypothesis.  This mirrors Paper III's own partial Latin square
completion (`TypedTriangle.Applications.Latin.Completion`), which takes the residual seed as an
explicit input (`ResidualVerificationInputs`, `FiniteSeedData`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

variable {a b c : ℕ}

/-- `P ∪ D` is an STS when `D` decomposes the residual host of the packing `P`. -/
theorem sts_of_packing_union (P D : Finset (Finset (Fin (a + b + c))))
    (hP : ∀ T ∈ P, IsAllowed (cdrHost a b c) cdrF T)
    (hPd : (P : Set (Finset (Fin (a + b + c)))).PairwiseDisjoint triEdges)
    (hD : IsDecomposition (rHost (col3 a b c) (P.biUnion triEdges)) cdrF
      (edges (rHost (col3 a b c) (P.biUnion triEdges))) D) :
    ∃ S : STS (Fin (a + b + c)), S.blocks = P ∪ D ∧ IsStrictBicolouring S (col3 a b c) ∧
      classSize (col3 a b c) 0 = a ∧ classSize (col3 a b c) 1 = b ∧
      classSize (col3 a b c) 2 = c := by
  obtain ⟨hall, hdisj, hcov⟩ := hD
  set L := P.biUnion triEdges with hL
  have hmem : ∀ (T : Finset (Fin (a + b + c))) (x y : Fin (a + b + c)), x ≠ y →
      (s(x, y) ∈ triEdges T ↔ x ∈ T ∧ y ∈ T) := by
    intro T x y hxy
    simp [triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff, hxy]
  -- every block has three points and is bicoloured
  have h3 : ∀ T ∈ P ∪ D, T.card = 3 ∧ (T.image (col3 a b c)).card = 2 := by
    intro T hT
    rcases mem_union.mp hT with h | h
    · exact ⟨(hP T h).1, (hP T h).2.2.2⟩
    · exact ⟨(hall T h).1, (hall T h).2.2.2⟩
  -- triangles of `D` avoid `L`
  have hDL : ∀ T ∈ D, ∀ e ∈ triEdges T, e ∉ L := by
    intro T hT e he heL
    have : e ∈ edges (rHost (col3 a b c) L) := by
      rw [← hcov]; simp only [Finset.mem_biUnion]; exact ⟨T, hT, he⟩
    induction e using Sym2.ind with
    | _ u v =>
    rw [mem_edges_rHost, rG_adj] at this
    exact this.1 heL
  refine ⟨⟨P ∪ D, fun T hT => (h3 T hT).1, fun x y hxy => ?_⟩, rfl, fun T hT => (h3 T hT).2,
    ?_, ?_, ?_⟩
  · by_cases hxL : s(x, y) ∈ L
    · obtain ⟨T, hT, he⟩ := mem_biUnion.mp hxL
      refine ⟨T, ⟨mem_union_left _ hT, (hmem T x y hxy).1 he⟩, ?_⟩
      rintro T' ⟨hT', hx', hy'⟩
      rcases mem_union.mp hT' with h | h
      · by_contra hne
        exact disjoint_left.1 (hPd h hT hne) ((hmem T' x y hxy).2 ⟨hx', hy'⟩) he
      · exact absurd hxL (hDL T' h _ ((hmem T' x y hxy).2 ⟨hx', hy'⟩))
    · have he : s(x, y) ∈ edges (rHost (col3 a b c) L) := by
        rw [mem_edges_rHost, rG_adj]; exact ⟨hxL, hxy⟩
      rw [← hcov] at he
      simp only [Finset.mem_biUnion] at he
      obtain ⟨T, hT, hxyT⟩ := he
      refine ⟨T, ⟨mem_union_right _ hT, (hmem T x y hxy).1 hxyT⟩, ?_⟩
      rintro T' ⟨hT', hx', hy'⟩
      rcases mem_union.mp hT' with h | h
      · exact absurd (mem_biUnion.mpr ⟨T', h, (hmem T' x y hxy).2 ⟨hx', hy'⟩⟩) hxL
      · by_contra hne
        exact disjoint_left.1 (hdisj h hT hne) ((hmem T' x y hxy).2 ⟨hx', hy'⟩) hxyT
  · rw [classSize, ← Fintype.card_subtype]; exact card_classA
  · rw [classSize, ← Fintype.card_subtype]; exact card_classB
  · rw [classSize, ← Fintype.card_subtype]; exact card_classC

/-- **Completion of sparse bicoloured packings, conditional on a residual diffuse seed.** -/
theorem cdr_completion_of_seed (C : ℝ) (hC : 1 ≤ C) :
    ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
      ∀ (P : Finset (Finset (Fin (a + b + c)))) (Δ : ℕ),
        (∀ T ∈ P, IsAllowed (cdrHost a b c) cdrF T) →
        (P : Set (Finset (Fin (a + b + c)))).PairwiseDisjoint triEdges →
        (∀ p, degL (P.biUnion triEdges) p ≤ Δ) → 64 * Δ + 64 ≤ a + b + c →
        (∃ μ, IsDiffuseSeed (rHost (col3 a b c) (P.biUnion triEdges)) cdrF C μ) →
        ∃ S : STS (Fin (a + b + c)), P ⊆ S.blocks ∧ IsStrictBicolouring S (col3 a b c) ∧
          classSize (col3 a b c) 0 = a ∧ classSize (col3 a b c) 1 = b ∧
          classSize (col3 a b c) 2 = c := by
  obtain ⟨n₀, hT⟩ := Vortex.main_theorem_T cdrF (1 / 32) C 6 (by norm_num) hC le_rfl
  refine ⟨max n₀ 400, fun a b c h hn P Δ hP hPd hdeg hΔ hseed => ?_⟩
  have h400 : 400 ≤ a + b + c := le_of_max_le_right hn
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h h400
  have hs0 := csz_col3 a b c 0
  have hs1 := csz_col3 a b c 1
  have hs2 := csz_col3 a b c 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hs0 hs1 hs2
  have hcls : ∀ k, Fintype.card (Fin (a + b + c)) + 8 ≤ 4 * csz (col3 a b c) k := by
    intro k; rw [Fintype.card_fin]
    fin_cases k
    · simpa [hs0] using ha4
    · simpa [hs1] using hb4
    · simpa [hs2] using hc4
  have hΔ' : 64 * Δ + 64 ≤ Fintype.card (Fin (a + b + c)) := by rw [Fintype.card_fin]; exact hΔ
  set L := P.biUnion triEdges with hL
  have hbig : BigR (col3 a b c) L := bigR_of_deg hdeg fun k => by
    have := hcls k; rw [Fintype.card_fin] at this; omega
  obtain ⟨o, ho, hoadj⟩ := exists_base hbig (⟨0, by omega⟩ : Fin (a + b + c))
  obtain ⟨h01, h02, h12⟩ := adm_even_mul h
  have hnodd : Even (Fintype.card (Fin (a + b + c)) - 1) := by
    rw [Fintype.card_fin, Nat.even_iff]; have := h.2.2.2.1; omega
  have hH2 : IsPhysical (rHost (col3 a b c) L) cdrF (edges (rHost (col3 a b c) L)) :=
    residual_physical hbig ho hoadj P hP hPd hL hnodd (by rw [hs0, hs1]; exact h01)
      (by rw [hs0, hs2]; exact h02) (by rw [hs1, hs2]; exact h12)
      (by rw [hs0, hs1, hs2]; exact h.2.2.2.2.1)
  obtain ⟨D, hD⟩ := hT (rHost (col3 a b c) L)
    (by rw [Fintype.card_fin]; exact le_of_max_le_left hn) hseed hH2
    (residual_H3 hdeg hcls hΔ') (residual_H4 hdeg hcls hΔ')
  obtain ⟨S, hS, hcol, ha, hb, hc⟩ := sts_of_packing_union P D hP hPd hD
  exact ⟨S, hS ▸ subset_union_left, hcol, ha, hb, hc⟩

/-- **Completion of sparse bicoloured packings** (backlog item 2a).  Every packing of
bicoloured triangles of a sufficiently large admissible profile, whose leave has maximum degree
at most `n / 6656000`, extends to a strictly bicoloured STS with the prescribed classes. -/
theorem cdr_completion :
    ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
      ∀ (P : Finset (Finset (Fin (a + b + c)))) (Δ : ℕ),
        (∀ T ∈ P, IsAllowed (cdrHost a b c) cdrF T) →
        (P : Set (Finset (Fin (a + b + c)))).PairwiseDisjoint triEdges →
        (∀ p, degL (P.biUnion triEdges) p ≤ Δ) → 6656000 * Δ ≤ a + b + c →
        ∃ S : STS (Fin (a + b + c)), P ⊆ S.blocks ∧ IsStrictBicolouring S (col3 a b c) ∧
          classSize (col3 a b c) 0 = a ∧ classSize (col3 a b c) 1 = b ∧
          classSize (col3 a b c) 2 = c := by
  obtain ⟨n₀, hT⟩ := cdr_completion_of_seed 8 (by norm_num)
  refine ⟨max n₀ 2040, fun a b c h hn P Δ hP hPd hdeg hΔ => ?_⟩
  have h2040 : 2040 ≤ a + b + c := le_of_max_le_right hn
  exact hT a b c h (le_of_max_le_left hn) P Δ hP hPd hdeg (by omega)
    (cdr_residual_seed h h2040 P hP hPd hdeg hΔ)

end CDRBicolour.Absorption
