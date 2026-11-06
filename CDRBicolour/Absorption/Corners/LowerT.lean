/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Corners.Lower
public import CDRBicolour.Absorption.Completion

/-!
# The lower corner of the block-type spectrum (item 3)

`corner_lower`: for every sufficiently large admissible profile and parameters `d, q, r` (degree of
the planted graph of each class, quotient and remainder of the apex counts) satisfying the exact
relations, the degree-`0` exception and a smallness condition, there is a strictly bicoloured STS
with the prescribed classes and exactly `c·q₂ + r₂` blocks of type `AAC`.

The planted minority packing is `lower_packing`; the residual host, balanced and with even
`σ`, is completed with majority triangles by Theorem T: H1 `corner_residual_seed`,
H2 `physical_maj`, H3/H4 `gen_H3`/`gen_H4`.
-/

@[expose] public section

noncomputable section

open Classical

namespace CDRBicolour.Absorption.Corners

open Finset SimpleGraph TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption
  CDRBicolour.Absorption.Refined CDRBicolour.BlockTypes

theorem sz_sum (a b c : ℕ) (X : Fin 3) : sz a b c X + sz a b c (X + 1) + sz a b c (X + 2) = a + b + c := by
  fin_cases X <;> simp [sz] <;> omega

theorem sz_csz (a b c : ℕ) (X : Fin 3) : csz (col3 a b c) X = sz a b c X := csz_col3 a b c X

/-- The leave degree in terms of the counts at the labels of `u`. -/
theorem degL_lab {a b c : ℕ} (P : Finset (Finset (Fin (a + b + c)))) (u : Fin (a + b + c)) :
    degL (P.biUnion triEdges) u = #(LN (col3 a b c) P u (col3 a b c u)) +
      #(LN (col3 a b c) P u (col3 a b c u + 1)) + #(LN (col3 a b c) P u (col3 a b c u + 2)) := by
  rw [degL_eq (lab := col3 a b c)]
  rcases (show col3 a b c u = 0 ∨ col3 a b c u = 1 ∨ col3 a b c u = 2 by omega) with h | h | h <;>
    rw [h] <;> simp <;> omega

/-- Residual counts at a vertex. -/
theorem res_counts {a b c : ℕ} (P : Finset (Finset (Fin (a + b + c)))) (u : Fin (a + b + c))
    (Y : Fin 3) :
    #(univ.filter fun v => (rG (P.biUnion triEdges)).Adj u v ∧ col3 a b c v = Y) =
      sz a b c Y - (if col3 a b c u = Y then 1 else 0) - #(LN (col3 a b c) P u Y) := by
  have := res_count (lab := col3 a b c) P u Y
  rw [sz_csz] at this
  omega

theorem allowed_of_shape {a b c : ℕ} {T : Finset (Fin (a + b + c))}
    (hT : ∃ X : Fin 3, ∃ u u' w, T = {u, u', w} ∧ u ≠ u' ∧ col3 a b c u = X ∧ col3 a b c u' = X ∧
      col3 a b c w = X + 2) : IsAllowed (cdrHost a b c) cdrF T := by
  obtain ⟨X, u, u', w, rfl, h1, hu, hu', hw⟩ := hT
  have h2 : u ≠ w := fun e => fin3_add2_ne X (by rw [← hw, ← e, hu])
  have h3 : u' ≠ w := fun e => fin3_add2_ne X (by rw [← hw, ← e, hu'])
  refine ⟨card_eq_three.2 ⟨u, u', w, h1, h2, h3, rfl⟩, fun x _ y _ hxy => hxy, ?_⟩
  show ({u, u', w} : Finset _).val.map (col3 a b c) ∈ cdrF
  rw [val_map_triple _ h1 h2.symm h3.symm, hu, hu', hw]
  exact minT_mem X

/-- Majority blocks are not of type `AAC`. -/
theorem maj_not_aac {a b c : ℕ} {L : Finset (Sym2 (Fin (a + b + c)))} {T : Finset (Fin (a + b + c))}
    (hT : IsAllowed (rHost (col3 a b c) L) majF T) :
    ¬ (cnt (col3 a b c) 0 T = 2 ∧ cnt (col3 a b c) 2 T = 1) := by
  obtain ⟨h3, -, Y, hY⟩ := hT
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.1 h3
  have hY' : ({col3 a b c p, col3 a b c q, col3 a b c r} : Multiset (Fin 3)) = {Y, Y, Y + 1} := by
    rw [← val_map_triple _ hpq hpr.symm hqr.symm]; exact hY
  clear hY
  rw [cnt_triple _ hpq hpr hqr, cnt_triple _ hpq hpr hqr]
  generalize col3 a b c p = x at hY' ⊢
  generalize col3 a b c q = y at hY' ⊢
  generalize col3 a b c r = z at hY' ⊢
  revert x y z Y; decide

theorem cls_arith {n Dg s : ℕ} (h1 : 10 ^ 13 * Dg ≤ n) (h2 : n + 8 ≤ 4 * s) (h3 : 400 ≤ n) :
    n + 1024 * (5 * (Dg + 1)) ≤ 1024 * s ∧ n + 32 * (5 * (Dg + 1)) ≤ 32 * s ∧ 4 * (Dg + 1) < s := by
  have h1' : 6000 * Dg ≤ n := le_trans (Nat.mul_le_mul_right Dg (by norm_num)) h1
  clear h1
  refine ⟨by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 4000000 in
/-- **The lower corner.** -/
theorem corner_lower : ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
    ∀ d q r : Fin 3 → ℕ, (∀ X, r X < sz a b c X) →
      (∀ X, (d X : ℤ) = sz a b c X - 1 - sz a b c (X + 1) + 2 * q X) →
      (∀ X, sz a b c X * d X + 2 * r X = 2 * (sz a b c (X + 2) * q (X + 2) + r (X + 2))) →
      (∀ X, ¬ (d X = 0 ∧ (r X = 1 ∨ r X = 2))) →
      (∀ X, 10 ^ 15 * (d X + q X + 1) ≤ a + b + c) →
      ∃ S : STS (Fin (a + b + c)), IsStrictBicolouring S (col3 a b c) ∧
        classSize (col3 a b c) 0 = a ∧ classSize (col3 a b c) 1 = b ∧
        classSize (col3 a b c) 2 = c ∧ typeCount S (col3 a b c) 0 2 = c * q 2 + r 2 := by
  obtain ⟨nT, hT⟩ := Vortex.main_theorem_T majF (1 / 1024) 8 6 (by norm_num) (by norm_num) le_rfl
  refine ⟨max nT (10 ^ 24), fun a b c h hn d q r hr hdq hE hex hsm => ?_⟩
  have hn24 : 10 ^ 24 ≤ a + b + c := le_of_max_le_right hn
  have h400 : 400 ≤ a + b + c := le_trans (by norm_num) hn24
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h h400
  have hszl : ∀ X, a + b + c + 8 ≤ 4 * sz a b c X := by
    intro X; fin_cases X <;> simpa [sz]
  have hnodd : (a + b + c) % 2 = 1 := by have := h.2.2.2.1; omega
  -- the planted packing
  obtain ⟨P, hsh, hPd, hcnt, hAAC⟩ := lower_packing h d q r hr hdq hE hex fun X => by
    have := hsm X; norm_num at this
    have := hszl X; have := hszl (X + 2); constructor <;> omega
  set L := P.biUnion triEdges with hL
  set Dg := 2 * (d 0 + d 1 + d 2 + q 0 + q 1 + q 2) + 6 with hDgdef
  have hsm' : ∀ X, 1000000000000000 * (d X + q X + 1) ≤ a + b + c := fun X => by
    have := hsm X; norm_num at this; exact this
  have hDgn : 10 ^ 13 * Dg ≤ a + b + c := by
    have := hsm' 0; have := hsm' 1; have := hsm' 2
    have : 10000000000000 * Dg ≤ a + b + c := by omega
    norm_num; exact this
  -- leave degrees
  have hdeg : ∀ p, degL L p ≤ Dg := by
    intro p
    rw [hL, degL_lab]
    obtain ⟨t, ht, h1, h2, h3⟩ := hcnt p
    have hdX : d (col3 a b c p) ≤ d 0 + d 1 + d 2 := by
      rcases (show col3 a b c p = 0 ∨ col3 a b c p = 1 ∨ col3 a b c p = 2 by omega) with e | e | e <;>
        rw [e] <;> omega
    have hqX : q (col3 a b c p) ≤ q 0 + q 1 + q 2 := by
      rcases (show col3 a b c p = 0 ∨ col3 a b c p = 1 ∨ col3 a b c p = 2 by omega) with e | e | e <;>
        rw [e] <;> omega
    rw [h1, h2, h3]; omega
  -- residual counts
  have hrc : ∀ u, ∃ t ≤ 1,
      #(univ.filter fun v => (rG L).Adj u v ∧ col3 a b c v = col3 a b c u) =
        sz a b c (col3 a b c u) - 1 - (d (col3 a b c u) + 2 * t) ∧
      #(univ.filter fun v => (rG L).Adj u v ∧ col3 a b c v = col3 a b c u + 1) =
        sz a b c (col3 a b c u + 1) - 2 * (q (col3 a b c u) + t) ∧
      #(univ.filter fun v => (rG L).Adj u v ∧ col3 a b c v = col3 a b c u + 2) =
        sz a b c (col3 a b c u + 2) - (d (col3 a b c u) + 2 * t) := by
    intro u
    obtain ⟨t, ht, h1, h2, h3⟩ := hcnt u
    refine ⟨t, ht, ?_, ?_, ?_⟩
    · rw [hL, res_counts, if_pos rfl, h1]
    · rw [hL, res_counts, if_neg (fin3_ne_add1 _).symm, h2]; rfl
    · rw [hL, res_counts, if_neg (fin3_add2_ne _).symm, h3]; rfl
  have hbal : ∀ u, #(univ.filter fun v => (rG L).Adj u v ∧ col3 a b c v = col3 a b c u) =
      #(univ.filter fun v => (rG L).Adj u v ∧ col3 a b c v = col3 a b c u + 1) := by
    intro u
    obtain ⟨t, ht, h1, h2, -⟩ := hrc u
    rw [h1, h2]
    set X := col3 a b c u
    have e := hdq X
    have s1 := hsm' X; have s2 := hszl X; have s3 := hszl (X + 1)
    omega
  have hpar : ∀ u, Even #(univ.filter fun v => (rG L).Adj u v ∧ col3 a b c v = col3 a b c u + 2) := by
    intro u
    obtain ⟨t, ht, -, -, h3⟩ := hrc u
    rw [h3, Nat.even_iff]
    set X := col3 a b c u
    have e := hdq X
    have s1 := hsm' X; have s2 := hszl (X + 2)
    have s4 := sz_sum a b c X
    omega
  -- H1
  have hres : ∀ v, ellG' (wpi (col3 a b c) v) (fun e : E0 (Fin (a + b + c)) =>
      if e.1 ∈ L then 0 else 1) = 0 := by
    intro v
    rw [ell_wpi_res, hbal v, sub_self]
  obtain ⟨μ, hμ⟩ := corner_residual_seed h hn24 L hres hdeg hDgn
  -- H2
  have hcls : ∀ k, 4 * (Dg + 1) < csz (col3 a b c) k := by
    intro k; rw [sz_csz]; exact (cls_arith hDgn (hszl k) h400).2.2
  have hbigR : BigR (col3 a b c) L := bigR_of_deg hdeg hcls
  have hexk : ∀ k, ∃ v, col3 a b c v = k := by
    intro k
    have hpos : 0 < csz (col3 a b c) k := by rw [sz_csz]; have := hszl k; omega
    obtain ⟨v, hv⟩ := card_pos.1 hpos
    exact ⟨v, (mem_filter.1 hv).2⟩
  have hH2 := physical_maj hbigR hexk hbal hpar
  -- H3, H4
  have hcls1024 : ∀ k, Fintype.card (Fin (a + b + c)) + 1024 * (5 * (Dg + 1)) ≤
      1024 * gsz (col3 a b c) k := by
    intro k
    rw [Fintype.card_fin]
    have e : gsz (col3 a b c) k = csz (col3 a b c) k := rfl
    rw [e, sz_csz]; exact (cls_arith hDgn (hszl k) h400).1
  have hcls32 : ∀ k, Fintype.card (Fin (a + b + c)) + 32 * (5 * (Dg + 1)) ≤
      32 * gsz (col3 a b c) k := by
    intro k
    rw [Fintype.card_fin]
    have e : gsz (col3 a b c) k = csz (col3 a b c) k := rfl
    rw [e, sz_csz]; exact (cls_arith hDgn (hszl k) h400).2.1
  have hH3 := gen_H3 (lab := col3 a b c) (L := L) majF (r := 1024) (by norm_num) hdeg hcls1024
  have hH4 := gen_H4 (lab := col3 a b c) (L := L) majF (r := 32) (by norm_num) hdeg hcls32
  have hH3' : CommonNbrCond (gHost (col3 a b c) L) majF (1 / 1024) := by convert hH3 using 2
  have hH4' : HingeCond (gHost (col3 a b c) L) majF (1 / 1024) 6 := by convert hH4 using 2
  -- Theorem T
  obtain ⟨D, hall, hdisj, hcov⟩ := hT (gHost (col3 a b c) L)
    (by rw [Fintype.card_fin]; exact le_of_max_le_left hn) ⟨μ, hμ⟩ hH2 hH3' hH4'
  have hD' : IsDecomposition (rHost (col3 a b c) L) cdrF (edges (rHost (col3 a b c) L)) D :=
    ⟨fun T hT => ⟨(hall T hT).1, (hall T hT).2.1, majF_sub (hall T hT).2.2⟩, hdisj, hcov⟩
  obtain ⟨S, hS, hcol, ha, hb, hc⟩ :=
    sts_of_packing_union P D (fun T hT => allowed_of_shape (hsh T hT)) hPd hD'
  refine ⟨S, hcol, ha, hb, hc, ?_⟩
  unfold typeCount
  rw [hS, filter_union]
  have hD0 : D.filter (fun B => cnt (col3 a b c) 0 B = 2 ∧ cnt (col3 a b c) 2 B = 1) = ∅ :=
    filter_false_of_mem fun T hT => maj_not_aac (hall T hT)
  rw [hD0, union_empty, hAAC]

end CDRBicolour.Absorption.Corners
