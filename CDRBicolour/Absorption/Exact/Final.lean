/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Exact.Copies
public import CDRBicolour.Absorption.Exact.Mass
public import CDRBicolour.Absorption.Refined.Seed
public import CDRBicolour.Absorption.Spectrum
public import CDRBicolour.Absorption.Completion
public import Mathlib.NumberTheory.Bertrand

/-!
# Exact block-type spectrum (backlog item 3)

**`cdr_aac_exact`**: for every `δ > 0` and every sufficiently large admissible profile, every
integer `t` for which the six block-type counts forced by `N_AAC = t` are at least `δ n²` is the
number of `AAC` blocks of some realisation — **exactly**.

Proof.
1. `m²` edge-disjoint copies of the `AAC` trade (`Exact/Copies`), `m` a prime of order `λ n`;
   their leave `L` does not depend on which half each copy uses.
2. Residual seeds with prescribed `AAC` mass: two count seeds `wtN (m₀ ∓ 2E)` corrected by the
   bounded inverse (`residual_seed_cdr`), and the convex combination of mass exactly `m₀`.
3. Theorem T+ with the `AAC` monitor on `K_n − L`: a decomposition `D` with
   `|N_AAC(D) − m₀| ≤ η n² ≤ M/4`, `M = m²`, `m₀ = t − 3M/2`.
4. Exactly `k = t − M − N_AAC(D) ∈ [0, M]` copies take the half with two `AAC` triangles.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Exact

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Refined
  CDRBicolour.BlockTypes

variable {a b c : ℕ}

theorem MincG_seed_one {μ : Finset (Fin (a + b + c)) → ℝ} {C : ℝ}
    (hμ : IsDiffuseSeed (cdrHost a b c) cdrF C μ) (e : E0 (Fin (a + b + c))) :
    MincG (col3 a b c) cdrF μ e = 1 := by
  have he : e.1 ∈ (cdrHost a b c).G.edgeSet := by
    show e.1 ∈ (⊤ : SimpleGraph (Fin (a + b + c))).edgeSet
    rw [SimpleGraph.edgeSet_top]; exact e.2
  have := hμ.2 e.1 he
  simp only [MincG, LinearMap.coe_mk, AddHom.coe_mk]
  convert this using 2
  ext T
  simp only [mem_filter]
  apply and_congr_left'
  rw [gmem_tri]
  classical
  unfold allowed
  simp only [mem_filter, mem_univ, true_and]
  exact Iff.rfl

/-- The CDR bounded inverse as a generic one. -/
def briG {K : ℝ} (B : BRI (col3 a b c) K) : BRIG (col3 a b c) cdrF (wl (col3 a b c)) K :=
  ⟨B.Φ, fun d hd => B.exact d hd, fun d hd => B.bound d hd⟩

/-- **Residual seed with controlled `AAC` mass.** -/
theorem residual_seed_cdr (h : AdmissibleProfile a b c) (hn : 2040 ≤ a + b + c)
    {ε τ : ℝ} (hε : 0 < ε)
    (h1 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntAAB a b c τ)
    (h2 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntAAC a b c τ)
    (h3 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntBBC a b c τ)
    (h4 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntABB a b c τ)
    (h5 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntACC a b c τ)
    (h6 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntBCC a b c τ)
    (P : Finset (Finset (Fin (a + b + c)))) (hP : ∀ T ∈ P, IsAllowed (cdrHost a b c) cdrF T)
    (hPd : (P : Set (Finset (Fin (a + b + c)))).PairwiseDisjoint triEdges) {Δ : ℕ}
    (hdeg : ∀ p, degL (P.biUnion triEdges) p ≤ Δ)
    (hΔ : 8 * 52000 * (64 + 1 / ε) ^ 2 * Δ ≤ ((a + b + c : ℕ) : ℝ)) :
    ∃ μ, IsDiffuseSeed (rHost (col3 a b c) (P.biUnion triEdges)) cdrF (2 * (64 + 1 / ε)) μ ∧
      |∑ Q ∈ allowed (rHost (col3 a b c) (P.biUnion triEdges)) cdrF, μ Q * wAAC a b c Q - τ| ≤
        (4 * 52000 + 1) * (64 + 1 / ε) * Δ * ((a + b + c : ℕ) : ℝ) := by
  have h400 : 400 ≤ a + b + c := by omega
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h h400
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
  obtain ⟨B⟩ := bri_of_balanced (lab := col3 a b c) (m := (a + b + c + 8) / 4)
    (fun k => by have := hcsz k; omega) (by omega) (by rw [Fintype.card_fin]; omega)
  set C : ℝ := 64 + 1 / ε with hC
  have hC1 : 1 ≤ C := by
    have h0 : 0 < 1 / ε := by positivity
    rw [hC]; linarith
  have hseed := cdr_H1_counts h h400 hε h1 h2 h3 h4 h5 h6
  set μ₀ : Finset (Fin (a + b + c)) → ℝ := fun T => wtN a b c τ (T.val.map (col3 a b c))
  have hNpos : 0 < Fintype.card (Fin (a + b + c)) := by rw [Fintype.card_fin]; omega
  have hP' : ∀ T ∈ P, T ∈ triG (col3 a b c) cdrF := fun T hT => gmem_tri.mpr (hP T hT)
  have hρ := gMinc_indP P hP' hPd
  obtain ⟨μ, ψ, hμ, rfl, hψ⟩ := gen_residual_seed' (P.biUnion triEdges)
    (lab := col3 a b c) (F := cdrF) (w := wl (col3 a b c))
    (fun T hT => wl_tri hT) (K := 52000) (C₀ := C) (η := 0) (by norm_num) hC1 le_rfl
    (briG B) (refined_hell1 h h400) (μ₀ := μ₀) (fun T hT => hseed.1 T (gmem_tri.mp hT))
    (fun e => by rw [MincG_seed_one hseed e]; simp) _ hρ hdeg hNpos
    (by rw [Fintype.card_fin]; simpa using hΔ)
  refine ⟨_, hμ, ?_⟩
  have hb0 : ∀ T ∈ tri (col3 a b c), |μ₀ T| ≤ C / ((a + b + c : ℕ) : ℝ) := by
    intro T hT
    obtain ⟨l, u⟩ := hseed.1 T (mem_tri.mp hT)
    rw [Fintype.card_fin] at l u
    rw [abs_of_nonneg (le_trans (by positivity) l)]
    exact u
  have hm := mass_residual (P.biUnion triEdges) hdeg hψ hb0 (by linarith)
  have htot : ∑ Q ∈ allowed (cdrHost a b c) cdrF, μ₀ Q * wAAC a b c Q = τ :=
    seedN_aac_total h h400 τ
  rw [htot] at hm
  refine hm.trans (le_of_eq ?_)
  rw [Fintype.card_fin]
  have hN : (0 : ℝ) < ((a + b + c : ℕ) : ℝ) := by exact_mod_cast (show 0 < a + b + c by omega)
  field_simp
  ring

/-! ### Constants -/

/-- The six counts move by `|τ − t|`. -/
theorem cnt_shift (a b c : ℕ) {t τ δ : ℝ} (N : ℝ) (hτ : |τ - t| ≤ δ / 2 * N ^ 2)
    (h1 : δ * N ^ 2 ≤ cntAAB a b c t) (h2 : δ * N ^ 2 ≤ cntAAC a b c t)
    (h3 : δ * N ^ 2 ≤ cntBBC a b c t) (h4 : δ * N ^ 2 ≤ cntABB a b c t)
    (h5 : δ * N ^ 2 ≤ cntACC a b c t) (h6 : δ * N ^ 2 ≤ cntBCC a b c t) :
    δ / 2 * N ^ 2 ≤ cntAAB a b c τ ∧ δ / 2 * N ^ 2 ≤ cntAAC a b c τ ∧
      δ / 2 * N ^ 2 ≤ cntBBC a b c τ ∧ δ / 2 * N ^ 2 ≤ cntABB a b c τ ∧
      δ / 2 * N ^ 2 ≤ cntACC a b c τ ∧ δ / 2 * N ^ 2 ≤ cntBCC a b c τ := by
  rw [abs_le] at hτ
  simp only [cntAAB, cntAAC, cntBBC, cntABB, cntACC, cntBCC] at *
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 4000000 in
/-- **Exact `AAC` spectrum.** -/
theorem cdr_aac_exact (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c → ∀ t : ℕ,
      (let N := ((a + b + c : ℕ) : ℝ); δ * N ^ 2 ≤ cntAAB a b c t ∧ δ * N ^ 2 ≤ cntAAC a b c t ∧
        δ * N ^ 2 ≤ cntBBC a b c t ∧ δ * N ^ 2 ≤ cntABB a b c t ∧
        δ * N ^ 2 ≤ cntACC a b c t ∧ δ * N ^ 2 ≤ cntBCC a b c t) →
      ∃ S : STS (Fin (a + b + c)), IsStrictBicolouring S (col3 a b c) ∧
        classSize (col3 a b c) 0 = a ∧ classSize (col3 a b c) 1 = b ∧
        classSize (col3 a b c) 2 = c ∧ typeCount S (col3 a b c) 0 2 = t := by
  -- constants
  set ε : ℝ := δ / 2 with hε
  have hε0 : 0 < ε := by positivity
  set C : ℝ := 64 + 1 / ε with hC
  have hC64 : 64 ≤ C := by
    have h0 : 0 < 1 / ε := by positivity
    rw [hC]; linarith
  have hCε : 1 / C ≤ ε := by
    rw [div_le_iff₀ (by linarith)]
    have : 1 ≤ (1 / ε) * ε := by field_simp; rfl
    nlinarith
  set lam : ℝ := 1 / (10 ^ 9 * C ^ 2) with hlam
  have hlam0 : 0 < lam := by positivity
  set η : ℝ := lam ^ 2 / 16 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨nT, hT⟩ := Vortex.main_theorem_T_with_triangle_monitors cdrF (1 / 32) (2 * C) η 6 0
    (by norm_num) (by linarith) le_rfl hη0
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, 64 / lam ≤ N1 := exists_nat_ge _
  refine ⟨max nT (max 2040 N1), fun a b c h hn t ht => ?_⟩
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := ht
  have hnT : nT ≤ a + b + c := le_of_max_le_left hn
  have h2040 : 2040 ≤ a + b + c := le_trans (le_max_left _ _) (le_of_max_le_right hn)
  have hnN1 : N1 ≤ a + b + c := le_trans (le_max_right _ _) (le_of_max_le_right hn)
  set N : ℝ := ((a + b + c : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by simp only [hN]; exact_mod_cast (show 0 < a + b + c by omega)
  have hlamN : 64 ≤ lam * N := by
    have : (64 / lam : ℝ) ≤ N := hN1.trans (by simp only [hN]; exact_mod_cast hnN1)
    rw [div_le_iff₀ hlam0] at this; linarith
  -- the prime `m`
  set r : ℕ := ⌊lam * N⌋₊ with hr
  have hr1 : lam * N - 1 < r := Nat.sub_one_lt_floor _
  have hr2 : (r : ℝ) ≤ lam * N := Nat.floor_le (by positivity)
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0] at hr1; push_cast at hr1; linarith
  obtain ⟨m, hmp, hrm, hm2⟩ := Nat.exists_prime_lt_and_le_two_mul r hr0
  haveI : Fact m.Prime := ⟨hmp⟩
  have hmR1 : lam * N - 1 < m := by
    have : (r : ℝ) < m := by exact_mod_cast hrm
    linarith
  have hmR2 : (m : ℝ) ≤ 2 * lam * N := by
    have : (m : ℝ) ≤ 2 * r := by exact_mod_cast hm2
    linarith
  have hmR1' : lam * N / 2 ≤ m := by linarith
  -- size facts
  have hlamε : lam ≤ ε / 10 ^ 9 := by
    have : lam = (1 / C) * (1 / (10 ^ 9 * C)) := by rw [hlam]; field_simp
    rw [this]
    have h1 : 1 / (10 ^ 9 * C) ≤ 1 / 10 ^ 9 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    calc (1 / C) * (1 / (10 ^ 9 * C)) ≤ ε * (1 / 10 ^ 9) :=
          mul_le_mul hCε h1 (by positivity) hε0.le
      _ = ε / 10 ^ 9 := by ring
  have hlamsmall : lam ≤ 1 / 10 ^ 12 := by
    rw [hlam, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h (by omega)
  have haR : N + 8 ≤ 4 * (a : ℝ) := by simp only [hN]; exact_mod_cast ha4
  have hbR : N + 8 ≤ 4 * (b : ℝ) := by simp only [hN]; exact_mod_cast hb4
  have hcR : N + 8 ≤ 4 * (c : ℝ) := by simp only [hN]; exact_mod_cast hc4
  have h6l : 6 * lam * N ≤ N / 4 := by
    have : 6 * lam ≤ 1 / 4 := by linarith
    nlinarith
  have h3m : (3 * m : ℝ) ≤ N / 4 := by linarith
  have hCopy : CopyCond a b c m := by
    refine ⟨by exact_mod_cast (show (8 : ℝ) < m by linarith), ?_, ?_, ?_⟩
    · have : (3 * m : ℝ) ≤ a := by linarith
      exact_mod_cast this
    · have : (3 * m : ℝ) ≤ b := by linarith
      exact_mod_cast this
    · have : (3 * m : ℝ) ≤ c := by linarith
      exact_mod_cast this
  -- the copies and their leave
  set L := leave hCopy with hLdef
  set P0 := packP hCopy (fun _ => false)
  have hP0L : P0.biUnion triEdges = L := packP_leave hCopy _
  have hdegL : ∀ p, degL L p ≤ 81 * m := degL_leave hCopy
  have hdeg0 : ∀ p, degL (P0.biUnion triEdges) p ≤ 81 * m := by rw [hP0L]; exact hdegL
  set Δ : ℕ := 81 * m with hΔdef
  have hΔR : (Δ : ℝ) ≤ 162 * lam * N := by
    simp only [hΔdef]; push_cast; nlinarith
  have hΔpos : (0 : ℝ) < Δ := by simp only [hΔdef]; push_cast; nlinarith
  set MR : ℝ := (m : ℝ) ^ 2 with hMR
  have hMlo : lam ^ 2 * N ^ 2 / 4 ≤ MR := by
    rw [hMR]; nlinarith
  have hMhi : MR ≤ 4 * lam ^ 2 * N ^ 2 := by rw [hMR]; nlinarith
  set E : ℝ := (4 * 52000 + 1) * C * Δ * N with hE
  have hEpos : 0 < E := by positivity
  have hEle : E ≤ ε * N ^ 2 / 20 := by
    have h1 : E ≤ (4 * 52000 + 1) * C * (162 * lam * N) * N := by
      rw [hE]; gcongr
    have h2 : C * lam ≤ ε / 10 ^ 9 * C := by nlinarith
    have h3 : (4 * 52000 + 1) * C * (162 * lam * N) * N =
        (4 * 52000 + 1) * 162 * (C * lam) * N ^ 2 := by ring
    have h4 : C * lam = 1 / (10 ^ 9 * C) := by rw [hlam]; field_simp
    have h5 : 1 / (10 ^ 9 * C) ≤ ε / 10 ^ 9 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := hCε; rw [div_le_iff₀ (by linarith)] at this; nlinarith
    nlinarith
  set m₀ : ℝ := (t : ℝ) - 3 / 2 * MR with hm₀
  have hshift : ∀ τ : ℝ, |τ - m₀| ≤ 2 * E → |τ - t| ≤ δ / 2 * N ^ 2 := by
    intro τ hτ
    rw [abs_le] at hτ ⊢
    have : 3 / 2 * MR ≤ ε * N ^ 2 / 4 := by
      have : lam ^ 2 ≤ ε / 100 := by nlinarith
      nlinarith
    constructor <;> nlinarith
  -- two residual seeds and their masses
  have hseedΔ : 8 * 52000 * (64 + 1 / ε) ^ 2 * Δ ≤ N := by
    rw [← hC]
    have : C ^ 2 * lam = 1 / 10 ^ 9 := by rw [hlam]; field_simp
    nlinarith
  have hres : ∀ τ : ℝ, |τ - m₀| ≤ 2 * E →
      ∃ μ, IsDiffuseSeed (rHost (col3 a b c) L) cdrF (2 * C) μ ∧
        |∑ Q ∈ allowed (rHost (col3 a b c) L) cdrF, μ Q * wAAC a b c Q - τ| ≤ E := by
    intro τ hτ
    obtain ⟨s1, s2, s3, s4, s5, s6⟩ := cnt_shift a b c N (hshift τ hτ) t1 t2 t3 t4 t5 t6
    rw [← hε] at s1 s2 s3 s4 s5 s6
    have := residual_seed_cdr h h2040 hε0 s1 s2 s3 s4 s5 s6 P0 (packP_allowed hCopy _)
      (packP_disj hCopy _) hdeg0 hseedΔ
    rw [hP0L] at this
    exact this
  obtain ⟨μ1, hμ1, hM1⟩ := hres (m₀ - 2 * E) (by rw [show m₀ - 2 * E - m₀ = -(2 * E) by ring,
    abs_neg, abs_of_pos (by positivity)])
  obtain ⟨μ2, hμ2, hM2⟩ := hres (m₀ + 2 * E) (by rw [show m₀ + 2 * E - m₀ = 2 * E by ring,
    abs_of_pos (by positivity)])
  set M1 := ∑ Q ∈ allowed (rHost (col3 a b c) L) cdrF, μ1 Q * wAAC a b c Q
  set M2 := ∑ Q ∈ allowed (rHost (col3 a b c) L) cdrF, μ2 Q * wAAC a b c Q
  rw [abs_le] at hM1 hM2
  have hgap : 0 < M2 - M1 := by linarith
  set θ := (m₀ - M1) / (M2 - M1) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hgap.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hgap]; linarith
  have hμ := seed_convex hμ1 hμ2 hθ0 hθ1
  have hmass : ∑ Q ∈ allowed (rHost (col3 a b c) L) cdrF,
      ((1 - θ) * μ1 Q + θ * μ2 Q) * wAAC a b c Q = m₀ := by
    have : ∀ Q, ((1 - θ) * μ1 Q + θ * μ2 Q) * wAAC a b c Q =
        (1 - θ) * (μ1 Q * wAAC a b c Q) + θ * (μ2 Q * wAAC a b c Q) := fun Q => by ring
    simp_rw [this]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    show (1 - θ) * M1 + θ * M2 = m₀
    rw [hθ]; field_simp; ring
  -- H2, H3, H4 for the residual host
  have hs0 := csz_col3 a b c 0
  have hs1 := csz_col3 a b c 1
  have hs2 := csz_col3 a b c 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hs0 hs1 hs2
  have hcsz : ∀ k, Fintype.card (Fin (a + b + c)) + 8 ≤ 4 * csz (col3 a b c) k := by
    intro k; rw [Fintype.card_fin]; fin_cases k
    · simpa [hs0] using ha4
    · simpa [hs1] using hb4
    · simpa [hs2] using hc4
  have hΔsmall : 64 * Δ + 64 ≤ Fintype.card (Fin (a + b + c)) := by
    rw [Fintype.card_fin]
    have : (64 * Δ + 64 : ℝ) ≤ N := by nlinarith
    simp only [hN] at this; exact_mod_cast this
  have hbigR : BigR (col3 a b c) L := bigR_of_deg hdegL fun k => by
    have h1 := hcsz k; have h2 := hΔsmall; rw [Fintype.card_fin] at h1 h2; omega
  obtain ⟨o, ho, hoadj⟩ := exists_base hbigR (⟨0, by omega⟩ : Fin (a + b + c))
  obtain ⟨h01, h02, h12⟩ := adm_even_mul h
  have hnodd : Even (Fintype.card (Fin (a + b + c)) - 1) := by
    rw [Fintype.card_fin, Nat.even_iff]; have := h.2.2.2.1; omega
  have hH2 : IsPhysical (rHost (col3 a b c) L) cdrF (edges (rHost (col3 a b c) L)) :=
    residual_physical hbigR ho hoadj P0 (packP_allowed hCopy _) (packP_disj hCopy _) hP0L.symm
      hnodd (by rw [hs0, hs1]; exact h01) (by rw [hs0, hs2]; exact h02)
      (by rw [hs1, hs2]; exact h12) (by rw [hs0, hs1, hs2]; exact h.2.2.2.2.1)
  -- Theorem T+
  obtain ⟨D, hD, hmon⟩ := hT (rHost (col3 a b c) L) (fun Q => (1 - θ) * μ1 Q + θ * μ2 Q)
    (by rw [Fintype.card_fin]; exact hnT) hμ hH2 (residual_H3 hdegL hcsz hΔsmall)
    (residual_H4 hdegL hcsz hΔsmall) Unit (fun _ Q => wAAC a b c Q) (by simp)
    (fun _ Q _ => by unfold wAAC; split_ifs <;> simp)
  have hm := hmon ()
  rw [hmass, Fintype.card_fin] at hm
  set ND : ℕ := #(D.filter fun Q => Q.val.map (col3 a b c) = aac) with hND
  have hNDsum : ∑ Q ∈ D, wAAC a b c Q = ND := by
    unfold wAAC; rw [sum_boole]
  rw [hNDsum, abs_le] at hm
  have hηN : η * N ^ 2 ≤ MR / 4 := by rw [hη]; nlinarith
  -- the number of copies to switch
  have hk1 : ND + m ^ 2 ≤ t := by
    have : (ND : ℝ) + MR ≤ t := by rw [hm₀] at hm; nlinarith
    rw [hMR] at this; exact_mod_cast this
  have hk2 : t ≤ ND + m ^ 2 + m ^ 2 := by
    have : (t : ℝ) ≤ ND + MR + MR := by rw [hm₀] at hm; nlinarith
    rw [hMR] at this; exact_mod_cast this
  set k := t - ND - m ^ 2 with hk
  have hkM : k ≤ #(univ : Finset (ZMod m × ZMod m)) := by
    rw [card_univ, Fintype.card_prod, ZMod.card, ← sq]; omega
  obtain ⟨Qs, -, hQs⟩ := exists_subset_card_eq hkM
  set σ : ZMod m × ZMod m → Bool := fun q => decide (q ∈ Qs)
  set P := packP hCopy σ
  have hPL : P.biUnion triEdges = L := packP_leave hCopy σ
  have hD' : IsDecomposition (rHost (col3 a b c) (P.biUnion triEdges)) cdrF
      (edges (rHost (col3 a b c) (P.biUnion triEdges))) D := by rw [hPL]; exact hD
  obtain ⟨S, hS, hcol, ha, hb, hc⟩ :=
    sts_of_packing_union P D (packP_allowed hCopy σ) (packP_disj hCopy σ) hD'
  refine ⟨S, hcol, ha, hb, hc, ?_⟩
  -- the exact count
  have hPD : Disjoint P D := by
    rw [Finset.disjoint_left]
    intro T hTP hTD
    have hA := (hD.1 T hTD)
    have hdisj : Disjoint (triEdges T) L := ((allowed_rHost_iff L).mp hA).2
    have hsub : triEdges T ⊆ L := by
      intro e he; rw [← hPL]; exact mem_biUnion.mpr ⟨T, hTP, he⟩
    obtain ⟨x, y, z, hxy, -, -, rfl⟩ := card_eq_three.mp (packP_allowed hCopy σ _ hTP).1
    have hmem : s(x, y) ∈ triEdges ({x, y, z} : Finset (Fin (a + b + c))) := by
      simp [triEdges, hxy]
    exact disjoint_left.mp hdisj hmem (hsub hmem)
  have hcount : (typeCount S (col3 a b c) 0 2 : ℝ) = t := by
    rw [typeCount_aac, hS, sum_union hPD]
    have h1 : ∑ Q ∈ P, (if Q.val.map (col3 a b c) = aac then (1 : ℝ) else 0) = m ^ 2 + k := by
      rw [packP_aac hCopy σ]
      have : ∀ q : ZMod m × ZMod m, (if σ q then (2 : ℝ) else 1) =
          1 + (if q ∈ Qs then 1 else 0) := fun q => by
        simp only [σ, decide_eq_true_eq]; split_ifs <;> norm_num
      simp_rw [this]
      rw [sum_add_distrib, sum_const, card_univ, Fintype.card_prod, ZMod.card, sum_boole,
        filter_mem_eq_inter, univ_inter, hQs]
      push_cast; ring
    have h2 : ∑ Q ∈ D, (if Q.val.map (col3 a b c) = aac then (1 : ℝ) else 0) = ND := hNDsum
    rw [h1, h2, hk]
    have : ND + m ^ 2 ≤ t := hk1
    push_cast [Nat.sub_sub, Nat.cast_sub (by omega : ND + m ^ 2 ≤ t)]
    ring
  exact_mod_cast hcount

end CDRBicolour.Absorption.Exact