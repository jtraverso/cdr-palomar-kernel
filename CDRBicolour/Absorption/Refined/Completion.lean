/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Refined.Seed
public import CDRBicolour.Absorption.Completion
public import CDRBicolour.Absorption.Intersection

/-!
# Refined completions and the prescribed exact intersection (backlog item 2b)

For the refined host (labels `(col3 v, v mod 6)`, allowed = bicoloured triangles of parity class
`j`) of the residual graph `K_n − E(P)`:

* H1 — `gen_residual_seed` with the refined bounded inverse `refined_bri` and the approximate
  seed `muJ` (the packing indicator enters through `psi1 ∘ psi1`, so `P` may have any parity);
* H2 — `refined_physical` from the CDR residual H2 (`residual_physical`);
* H3, H4 — `gen_H3`, `gen_H4` with the refined class sizes `≥ ⌊len/6⌋`.

Theorem T (`main_theorem_T`, labels `Fin 3 × Fin 6`) decomposes the residual host:
`refined_completion j : RefinedCompletion j`.  With the reduction of `Intersection.lean`:

**`cdr_prescribed_intersection : PrescribedIntersection`** — two strictly bicoloured STS with the
prescribed classes meeting in exactly a given sparse bicoloured packing.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Refined

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

/-- Constant of the refined bounded inverse. -/
def KJ : ℕ := 32929 ^ 2 * 52000

theorem gsz_rlab {a b c : ℕ} (X : Fin 3) (r : Fin 6) :
    clen a b c X / 6 ≤ gsz (rlab a b c) (X, r) := by
  refine (card_class_res (a := a) (b := b) (c := c) X r.isLt).trans (le_of_eq ?_)
  unfold gsz
  congr 1

theorem clen_lower {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c) (X : Fin 3) :
    a + b + c + 8 ≤ 4 * clen a b c X := by
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h hn
  fin_cases X <;> simp [clen] <;> omega

/-- Arithmetic of the class bounds. -/
theorem arith_cls {n Δ cl g : ℕ} (h1 : 2040 ≤ n) (h2 : 1024 * Δ ≤ n) (h3 : n + 8 ≤ 4 * cl)
    (h4 : cl / 6 ≤ g) : n + 1024 * (5 * (Δ + 1)) ≤ 1024 * g ∧ n + 32 * (5 * (Δ + 1)) ≤ 32 * g ∧
      4 * (Δ + 1) < g := by
  omega

/-- **Refined completion in parity class `j`.** -/
theorem refined_completion (j : ℕ) (hj : j < 2) : RefinedCompletion j := by
  obtain ⟨nT, hT⟩ := Vortex.main_theorem_T (refF j) (1 / 1024) 16 6 (by norm_num) (by norm_num)
    le_rfl
  refine ⟨1024 * KJ, max nT (5376 * KJ + 2040), fun a b c h hn P Δ hP hPd hdeg hK => ?_⟩
  have hn1 : 5376 * KJ + 2040 ≤ a + b + c := le_of_max_le_right hn
  have hKJ : 1 ≤ KJ := by unfold KJ; norm_num
  have hΔ1 : 1024 * Δ ≤ a + b + c := by
    refine le_trans ?_ hK
    calc 1024 * Δ = 1024 * 1 * Δ := by ring
      _ ≤ 1024 * KJ * Δ := by gcongr
  have h2040 : 2040 ≤ a + b + c := le_trans (Nat.le_add_left _ _) hn1
  have h400 : 400 ≤ a + b + c := by omega
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h h400
  have hbig : BigCls a b c := ⟨by omega, by omega, by omega⟩
  have hcl := clen_lower h h400
  set L := P.biUnion triEdges with hL
  have hP' : ∀ T ∈ P, T ∈ tri (col3 a b c) := fun T hT => mem_tri.mpr (hP T hT)
  have hs0 := csz_col3 a b c 0
  have hs1 := csz_col3 a b c 1
  have hs2 := csz_col3 a b c 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hs0 hs1 hs2
  have hcsz : ∀ k, a + b + c + 8 ≤ 4 * csz (col3 a b c) k := by
    intro k; fin_cases k
    · simpa [hs0] using ha4
    · simpa [hs1] using hb4
    · simpa [hs2] using hc4
  have hNpos : 0 < Fintype.card (Fin (a + b + c)) := by rw [Fintype.card_fin]; omega
  have hNR : (0 : ℝ) < Fintype.card (Fin (a + b + c)) := by exact_mod_cast hNpos
  -- H1
  obtain ⟨B⟩ := bri_of_balanced (lab := col3 a b c) (m := (a + b + c + 8) / 4)
    (fun k => by have := hcsz k; omega) (by omega) (by rw [Fintype.card_fin]; omega)
  have hρ : ∀ e : E0 (Fin (a + b + c)), MincG (rlab a b c) (refF j)
      (psi1 j (psi1 j fun T => if T ∈ P then 1 else 0)) e = if e.1 ∈ L then 1 else 0 := by
    intro e
    rw [MincG_eq j hj _ (fun T hT => psi2_zero hbig j hj _ hT), Minc_psi1 hbig, Minc_psi1 hbig,
      Minc_indP P hP' hPd e]
  have hΔR : 8 * ((32929 : ℝ) ^ 2 * 52000) * 8 ^ 2 * Δ +
      4 * ((32929 : ℝ) ^ 2 * 52000) * 8 * (84 / Fintype.card (Fin (a + b + c))) *
        Fintype.card (Fin (a + b + c)) ≤ Fintype.card (Fin (a + b + c)) := by
    have e1 : 4 * ((32929 : ℝ) ^ 2 * 52000) * 8 * (84 / Fintype.card (Fin (a + b + c))) *
        Fintype.card (Fin (a + b + c)) = 2688 * ((32929 : ℝ) ^ 2 * 52000) := by
      field_simp; ring
    rw [e1]
    have hB' : 5376 * KJ ≤ a + b + c := le_trans (Nat.le_add_right _ _) hn1
    have hA : ((1024 * KJ * Δ : ℕ) : ℝ) ≤ ((a + b + c : ℕ) : ℝ) := Nat.cast_le.mpr hK
    have hB : ((5376 * KJ : ℕ) : ℝ) ≤ ((a + b + c : ℕ) : ℝ) := Nat.cast_le.mpr hB'
    have hKR : ((KJ : ℕ) : ℝ) = (32929 : ℝ) ^ 2 * 52000 := by unfold KJ; push_cast; ring
    rw [Nat.cast_mul, Nat.cast_mul, hKR] at hA
    rw [Nat.cast_mul, hKR] at hB
    rw [Fintype.card_fin]
    generalize (32929 : ℝ) ^ 2 * 52000 = Kr at hA hB ⊢
    push_cast at hA hB ⊢
    nlinarith
  obtain ⟨μ, hμ⟩ := gen_residual_seed L (refined_hw j hj) (K := (32929 : ℝ) ^ 2 * 52000)
    (C₀ := 8) (η := 84 / Fintype.card (Fin (a + b + c))) (by positivity) (by norm_num)
    (by positivity) (refined_bri hbig j hj (by norm_num) B) (refined_hell1 h h400)
    (fun T hT => muJ_bounds h h400 j hj hT) (muJ_deficit h h400 j hj) _ hρ hdeg hNpos hΔR
  have hseed : ∃ μ, IsDiffuseSeed (gHost (rlab a b c) L) (refF j) 16 μ :=
    ⟨μ, by convert hμ using 1; norm_num⟩
  -- H2
  have hbigR : BigR (col3 a b c) L := bigR_of_deg hdeg fun k => by have := hcsz k; omega
  obtain ⟨o, ho, hoadj⟩ := exists_base hbigR (⟨0, by omega⟩ : Fin (a + b + c))
  obtain ⟨h01, h02, h12⟩ := adm_even_mul h
  have hnodd : Even (Fintype.card (Fin (a + b + c)) - 1) := by
    rw [Fintype.card_fin, Nat.even_iff]; have := h.2.2.2.1; omega
  have hphys : IsPhysical (rHost (col3 a b c) L) cdrF (edges (rHost (col3 a b c) L)) :=
    residual_physical hbigR ho hoadj P hP hPd hL hnodd (by rw [hs0, hs1]; exact h01)
      (by rw [hs0, hs2]; exact h02) (by rw [hs1, hs2]; exact h12)
      (by rw [hs0, hs1, hs2]; exact h.2.2.2.2.1)
  have hbigRef : BigRef (col3 a b c) b6 L := bigRef_of_deg hdeg fun k => by
    obtain ⟨X, r⟩ := k
    show 4 * (Δ + 1) < gsz (rlab a b c) (X, r)
    exact (arith_cls h2040 hΔ1 (hcl X) (gsz_rlab X r)).2.2
  have hH2 := refined_physical hbigRef j hj hphys
  -- H3, H4
  have hcls1024 : ∀ k : Fin 3 × Fin 6,
      Fintype.card (Fin (a + b + c)) + 1024 * (5 * (Δ + 1)) ≤ 1024 * gsz (rlab a b c) k := by
    intro k
    obtain ⟨X, s⟩ := k
    rw [Fintype.card_fin]
    exact (arith_cls h2040 hΔ1 (hcl X) (gsz_rlab X s)).1
  have hcls32 : ∀ k : Fin 3 × Fin 6,
      Fintype.card (Fin (a + b + c)) + 32 * (5 * (Δ + 1)) ≤ 32 * gsz (rlab a b c) k := by
    intro k
    obtain ⟨X, s⟩ := k
    rw [Fintype.card_fin]
    exact (arith_cls h2040 hΔ1 (hcl X) (gsz_rlab X s)).2.1
  have hH3 := gen_H3 (lab := rlab a b c) (L := L) (refF j) (r := 1024) (by norm_num) hdeg hcls1024
  have hH4 := gen_H4 (lab := rlab a b c) (L := L) (refF j) (r := 32) (by norm_num) hdeg hcls32
  have hH3' : CommonNbrCond (gHost (rlab a b c) L) (refF j) (1 / 1024) := by
    convert hH3 using 2
  have hH4' : HingeCond (gHost (rlab a b c) L) (refF j) (1 / 1024) 6 := by
    convert hH4 using 2
  -- Theorem T
  obtain ⟨D, hall, hdisj, hcov⟩ := hT (gHost (rlab a b c) L)
    (by rw [Fintype.card_fin]; exact le_of_max_le_left hn) hseed hH2 hH3' hH4'
  have hD' : IsDecomposition (rHost (col3 a b c) L) cdrF (edges (rHost (col3 a b c) L)) D := by
    refine ⟨fun T hT => ⟨(hall T hT).1, (hall T hT).2.1, ?_⟩, hdisj, hcov⟩
    have := (hall T hT).2.2
    have h1 : (T.val.map (rlab a b c)).map Prod.fst ∈ cdrF := this.1
    rwa [rlab_map_fst] at h1
  obtain ⟨S, hS, hcol, ha, hb, hc⟩ := sts_of_packing_union P D hP hPd hD'
  refine ⟨S, hS ▸ subset_union_left, hcol, ha, hb, hc, fun T hTS hTP => ?_⟩
  rw [hS] at hTS
  have hTD : T ∈ D := by
    rcases mem_union.mp hTS with h' | h'
    · exact absurd h' hTP
    · exact h'
  have := (hall T hTD).2.2
  have h2 : ((T.val.map (rlab a b c)).map fun l => (l.2 : ℕ)).sum % 6 / 3 = j := this.2
  rw [rlab_sum] at h2
  exact h2

/-- **Backlog item 2b: prescribed exact intersection.** For every sufficiently large admissible
profile and every sparse packing `P` of bicoloured triangles, there are two strictly bicoloured
STS with the prescribed classes whose block sets intersect in exactly `P`. -/
theorem cdr_prescribed_intersection : PrescribedIntersection :=
  prescribed_intersection_of_refined (refined_completion 0 (by norm_num))
    (refined_completion 1 (by norm_num))

end CDRBicolour.Absorption.Refined
