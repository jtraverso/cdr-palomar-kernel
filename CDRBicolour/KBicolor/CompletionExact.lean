/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.ReservedSpectrum

/-! # Sparse completion with prescribed exact interior type counts -/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Exact
  CDRBicolour.Absorption.Refined

set_option maxHeartbeats 8000000 in
/-- Sparse completion with prescribed exact interior type counts. -/
theorem kbicolour_completion_types_exact (k : ℕ) (hk : 3 ≤ k) {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ X, δ * n ≤ ksz lab X) →
      (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X - 1) = n * (n - 1) →
      ∀ t : Fin k → Fin k → ℕ,
      (∀ X Y, X ≠ Y → 2 * (t X Y + t Y X) = ksz lab X * ksz lab Y) →
      (∀ X, 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y = ksz lab X * (ksz lab X - 1)) →
      (∀ X Y, X ≠ Y → ε * (n : ℝ) ^ 2 ≤ t X Y) →
      ∀ (Q : Finset (Finset (Fin n))) (ΔQ : ℕ),
      (∀ T ∈ Q, IsAllowed (kHost lab) (bicF k) T) →
      (Q : Set (Finset (Fin n))).PairwiseDisjoint triEdges →
      (∀ p, degL (Q.biUnion triEdges) p ≤ ΔQ) → (ΔQ : ℝ) ≤ γ * n →
      ∃ D : Finset (Finset (Fin n)), IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D ∧
        Q ⊆ D ∧ ∀ X Y, X ≠ Y → kTypeCount lab D X Y = t X Y := by
  classical
  -- constants
  set o : Fin k := ⟨0, by omega⟩ with ho
  set Jc : ℝ := (Fintype.card (Coord o) : ℝ) with hJc
  have hJc0 : 0 ≤ Jc := Nat.cast_nonneg _
  set R : ℝ := 2 / δ with hR
  have hR2 : 2 ≤ R := by rw [hR, le_div_iff₀ hδ]; linarith
  have hR1 : 1 ≤ R := by linarith
  set η : ℝ := ε / 2 with hη
  have hη0 : 0 < η := by positivity
  set C₀ : ℝ := 1 / η + 2 / δ with hC₀
  have hC₀1 : 1 ≤ C₀ := by
    have : 2 ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
    have : 0 < 1 / η := by positivity
    linarith
  set Kc : ℝ := (#(Trip o) : ℝ) * (400 * R ^ 5 * R * (1 + 4 * R ^ 2)) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set B : ℝ := 1 + 144 * Kc * C₀ ^ 2 + 480 * (Jc + 1) / ε + 216 * (Jc + 1) * (4 * Kc + 1) * C₀ / ε +
    18 * (Jc + 1) / δ + 360 / δ + 36 * ((k : ℝ) + 4) / δ with hB
  have tB1 : 0 ≤ 144 * Kc * C₀ ^ 2 := by positivity
  have tB2 : 0 ≤ 480 * (Jc + 1) / ε := by positivity
  have tB3 : 0 ≤ 216 * (Jc + 1) * (4 * Kc + 1) * C₀ / ε := by positivity
  have tB4 : 0 ≤ 18 * (Jc + 1) / δ := by positivity
  have tB5 : 0 ≤ 360 / δ := by positivity
  have tB6 : 0 ≤ 36 * ((k : ℝ) + 4) / δ := by positivity
  have hBpos : 0 < B := by linarith
  set lam : ℝ := 1 / B with hlam
  have hlam0 : 0 < lam := by positivity
  have hlam1 : lam ≤ 1 := by
    have := le_of_mul_inv hBpos hlam (show (1 : ℝ) ≤ B by linarith); linarith
  have L1 : 144 * Kc * C₀ ^ 2 * lam ≤ 1 := le_of_mul_inv hBpos hlam (by linarith)
  have L2 : 480 * (Jc + 1) * lam ≤ ε := by
    have := le_of_mul_inv hBpos hlam (show 480 * (Jc + 1) / ε ≤ B by linarith)
    rw [div_mul_eq_mul_div, div_le_one hε] at this; exact this
  have L3 : 216 * (Jc + 1) * (4 * Kc + 1) * C₀ * lam ≤ ε := by
    have := le_of_mul_inv hBpos hlam
      (show 216 * (Jc + 1) * (4 * Kc + 1) * C₀ / ε ≤ B by linarith)
    rw [div_mul_eq_mul_div, div_le_one hε] at this; exact this
  have L4 : 18 * (Jc + 1) * lam ≤ δ := by
    have := le_of_mul_inv hBpos hlam (show 18 * (Jc + 1) / δ ≤ B by linarith)
    rw [div_mul_eq_mul_div, div_le_one hδ] at this; exact this
  have L5 : 360 * lam ≤ δ := by
    have := le_of_mul_inv hBpos hlam (show 360 / δ ≤ B by linarith)
    rw [div_mul_eq_mul_div, div_le_one hδ] at this; exact this
  have L6 : 36 * ((k : ℝ) + 4) * lam ≤ δ := by
    have := le_of_mul_inv hBpos hlam (show 36 * ((k : ℝ) + 4) / δ ≤ B by linarith)
    rw [div_mul_eq_mul_div, div_le_one hδ] at this; exact this
  set γ : ℝ := lam ^ 2 / 256 with hγ
  have hγ0 : 0 < γ := by positivity
  have hγlam : γ ≤ lam := by
    rw [hγ]
    have hsq := ar_sq hlam0 hlam1
    linarith
  set ηT : ℝ := lam ^ 2 / 512 with hηT
  have hηT0 : 0 < ηT := by positivity
  obtain ⟨nT, hT⟩ := Vortex.main_theorem_T_with_triangle_monitors (bicF k) (δ ^ 2 / 4) (2 * C₀)
    ηT 6 2 (by positivity) (by linarith) le_rfl hηT0
  set N₁ : ℝ := (513 + 64 * R ^ 3) / δ + 128 / lam + 12 * (Jc + 1) / ε + 20 / δ +
    2 * ((k : ℝ) + 4) / δ + k + 1 with hN₁
  have u1 : 0 ≤ (513 + 64 * R ^ 3) / δ := by positivity
  have u2 : 0 ≤ 128 / lam := by positivity
  have u3 : 0 ≤ 12 * (Jc + 1) / ε := by positivity
  have u4 : 0 ≤ 20 / δ := by positivity
  have u5 : 0 ≤ 2 * ((k : ℝ) + 4) / δ := by positivity
  have u6 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨γ, hγ0, max nT ⌈N₁⌉₊, fun n lab hn hodd hcls heven hdiv t htp htr htl
    Q ΔQ hQall hQdisj hQdeg hQΔ => ?_⟩
  have hnN : N₁ ≤ n := (Nat.ceil_le.1 (le_of_max_le_right hn))
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hkn : (k : ℝ) ≤ n := by linarith
  have hδn : 513 + 64 * R ^ 3 ≤ δ * n := by
    have h : (513 + 64 * R ^ 3) / δ ≤ n := by linarith
    rw [div_le_iff₀ hδ] at h; linarith
  have hlamn : 128 ≤ lam * n := by
    have h : 128 / lam ≤ n := by linarith
    rw [div_le_iff₀ hlam0] at h; linarith
  have hεn : 12 * (Jc + 1) ≤ ε * n := by
    have h : 12 * (Jc + 1) / ε ≤ n := by linarith
    rw [div_le_iff₀ hε] at h; linarith
  have hδn20 : 20 ≤ δ * n := by
    have h : 20 / δ ≤ n := by linarith
    rw [div_le_iff₀ hδ] at h; linarith
  have hδnk : 2 * ((k : ℝ) + 4) < δ * n := by
    have h : 2 * ((k : ℝ) + 4) / δ < n := by linarith
    rw [div_lt_iff₀ hδ] at h; linarith
  have hcard : (Fintype.card (Fin n) : ℝ) = n := by simp
  have hcls' : ∀ X, δ * Fintype.card (Fin n) ≤ ksz lab X := by
    intro X; rw [hcard]; exact hcls X
  have hkszn : ∀ X, (ksz lab X : ℝ) ≤ n := by
    intro X
    have : ksz lab X ≤ n := by
      unfold ksz; exact (card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  -- the prime
  set r : ℕ := ⌊lam * n / 2⌋₊ with hr
  have hr1 : lam * n / 2 - 1 < r := Nat.sub_one_lt_floor _
  have hr2 : (r : ℝ) ≤ lam * n / 2 := Nat.floor_le (by positivity)
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0] at hr1; push_cast at hr1; linarith
  obtain ⟨mp, hmp, hrm, hm2⟩ := Nat.exists_prime_lt_and_le_two_mul r hr0
  haveI : Fact mp.Prime := ⟨hmp⟩
  haveI : NeZero mp := ⟨hmp.ne_zero⟩
  have hmR1 : lam * n / 2 - 1 < mp := by
    have : (r : ℝ) < mp := by exact_mod_cast hrm
    linarith
  have hmR2 : (mp : ℝ) ≤ lam * n := by
    have : (mp : ℝ) ≤ 2 * r := by exact_mod_cast hm2
    linarith
  have hmlo : lam * n / 4 ≤ mp := by linarith
  have hm8 : 8 < mp := by
    have : (8 : ℝ) < mp := by linarith
    exact_mod_cast this
  have hmp0 : (0 : ℝ) ≤ mp := Nat.cast_nonneg _
  -- the placement and the leave
  have hplace : ∀ X, 9 * Fintype.card (Coord o) * mp ≤ ksz lab X := by
    intro X
    have : (9 * Fintype.card (Coord o) * mp : ℝ) ≤ ksz lab X :=
      ar_place hJc0 hlam0.le hn0.le (by linarith : (mp : ℝ) ≤ 2 * lam * n) L4 (hcls X)
    exact_mod_cast this
  obtain ⟨P, hPτ⟩ := exists_place lab (tau3 o) (tau3_inj o) hplace
  set S := goodCopies P (Q.biUnion triEdges) with hS
  set LR := leaveSelected P S with hLR
  have hLRQ : Disjoint LR (Q.biUnion triEdges) := leaveSelected_good_disjoint P _
  set L := LR ∪ Q.biUnion triEdges with hL
  set Δ : ℕ := 9 * mp + ΔQ with hΔ
  have hQn : (ΔQ : ℝ) ≤ lam * n :=
    hQΔ.trans (mul_le_mul_of_nonneg_right hγlam hn0.le)
  have hdegL : ∀ p, degL L p ≤ Δ := fun p =>
    (degL_union_le LR (Q.biUnion triEdges) p).trans
      (Nat.add_le_add (degL_leaveSelected P S p) (hQdeg p))
  have hΔR : (Δ : ℝ) ≤ 18 * lam * n := by
    simp only [hΔ]; push_cast; nlinarith only [hmR2, hQn, hmp0]
  set PR := packSelected P S (fun _ => false) with hPR
  have hPRL : PR.biUnion triEdges = LR := packSelected_leave P S _
  have hPRall := packSelected_allowed P S (fun _ => false)
  have hPRdisj := packSelected_disj P hm8 S (fun _ => false)
  have hQne : ∀ T ∈ Q, (triEdges T).Nonempty := by
    intro T hT
    obtain ⟨x, y, z, hxy, _, _, rfl⟩ := card_eq_three.mp (hQall T hT).1
    exact ⟨s(x,y), by simp [triEdges, hxy]⟩
  have hQcount : #Q ≤ n * ΔQ :=
    (card_packing_le_edges Q hQne hQdisj).trans (by
      simpa using card_edges_le_degree_sum (Q.biUnion triEdges) hQdeg)
  set P0 := PR ∪ Q with hP0
  have hP0L : P0.biUnion triEdges = L := by
    rw [hP0, union_biUnion, hPRL]
  have hP0all : ∀ T ∈ P0, IsAllowed (kHost lab) (bicF k) T :=
    fun T hT => (mem_union.mp hT).elim (hPRall T) (hQall T)
  have hP0disj : (P0 : Set (Finset (Fin n))).PairwiseDisjoint triEdges := by
    intro T hT U hU hne
    rcases mem_union.mp hT with hT | hT <;> rcases mem_union.mp hU with hU | hU
    · exact hPRdisj hT hU hne
    · have ht : triEdges T ⊆ LR := fun e he => by
        rw [← hPRL]; exact mem_biUnion.mpr ⟨T, hT, he⟩
      exact hLRQ.mono ht (fun e he => mem_biUnion.mpr ⟨U, hU, he⟩)
    · have hu : triEdges U ⊆ LR := fun e he => by
        rw [← hPRL]; exact mem_biUnion.mpr ⟨U, hU, he⟩
      exact (hLRQ.mono hu (fun e he => mem_biUnion.mpr ⟨T, hT, he⟩)).symm
    · exact hQdisj hT hU hne
  have hdeg0 : ∀ p, degL (P0.biUnion triEdges) p ≤ Δ := by rw [hP0L]; exact hdegL
  let g : Coord o → ℕ := fun i => #(S.filter fun c => c.1 = i)
  have hg : ∀ i, (mp : ℝ)^2 / 2 ≤ g i ∧ ηT * (n : ℝ)^2 ≤ (g i : ℝ) / 4 := by
    intro i
    have hcap := good_coordinate_capacity P hm8 (Q.biUnion triEdges) i
    have hcard := card_edges_le_degree_sum (Q.biUnion triEdges) hQdeg
    have hcapR : (mp : ℝ)^2 ≤ (g i : ℝ) + n * ΔQ := by
      have : mp^2 ≤ g i + n*ΔQ := hcap.trans (Nat.add_le_add_left (by simpa using hcard) _)
      exact_mod_cast this
    exact retained_capacity_margin hlam0.le hn0.le hmlo (by simpa only [hγ] using hQΔ) hcapR
  -- the bounded right inverse
  set mB : ℕ := ⌊δ * n⌋₊ with hmB
  have hmB1 : δ * n - 1 < mB := Nat.sub_one_lt_floor _
  have hmB2 : (mB : ℝ) ≤ δ * n := Nat.floor_le (by positivity)
  have hmBk : ∀ X, mB ≤ ksz lab X := by
    intro X; have : (mB : ℝ) ≤ ksz lab X := hmB2.trans (hcls X); exact_mod_cast this
  have h512 : 512 ≤ mB := by
    have : (512 : ℝ) ≤ mB := by
      have := pow_nonneg (show (0 : ℝ) ≤ R by linarith) 3; linarith
    exact_mod_cast this
  have hmR : 64 * R ^ 3 ≤ mB := by linarith
  have hbal : (Fintype.card (Fin n) : ℝ) ≤ R * mB := by
    rw [hcard, hR]
    exact ar_bal hδ hmB1 (by linarith)
  -- the target of the residual seed
  set s : Coord o → ℝ := fun j => (g j : ℝ) / 2 - selectedBase lab o P S j -
    kTypeCount lab Q j.1.1 j.1.2 with hs
  have hsb : ∀ j, |s j| ≤ 38 * lam ^ 2 * n ^ 2 := by
    intro j
    have hB : selectedBase lab o P S j ≤ 9 * mp^2 :=
      (selectedBase_le_Bn lab o P S j).trans (Bn_le lab o P hPτ j)
    have hp : kTypeCount lab Q j.1.1 j.1.2 ≤ n * ΔQ :=
      (card_filter_le _ _).trans hQcount
    exact prescribed_shift_budget hlam0.le hn0.le hmp0 hmR2 (by simpa only [hγ] using hQΔ)
      (Nat.cast_nonneg _) (by exact_mod_cast selected_coordinate_le S j)
      (Nat.cast_nonneg _) (by exact_mod_cast hB) (Nat.cast_nonneg _) (by exact_mod_cast hp)
  set t₀ := tsh o (fun A B => (t A B : ℝ)) s with ht₀
  have hpair₀ : ∀ X Y, X ≠ Y → 2 * (t₀ X Y + t₀ Y X) = (ksz lab X : ℝ) * ksz lab Y := by
    intro X Y h
    rw [ht₀, tsh_pair]
    have := htp X Y h
    exact_mod_cast this
  have hrow₀ : ∀ X, 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t₀ X Y =
      (ksz lab X : ℝ) * ((ksz lab X : ℝ) - 1) := by
    intro X
    rw [ht₀, tsh_row]
    have h1 : 1 ≤ ksz lab X := by
      have : (1 : ℝ) ≤ ksz lab X := by linarith [hcls X]
      exact_mod_cast this
    have := htr X
    have h' : ((2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y : ℕ) : ℝ) =
        ((ksz lab X * (ksz lab X - 1) : ℕ) : ℝ) := by rw [this]
    push_cast [Nat.cast_sub h1] at h'
    exact h'
  set ρ : ℝ := (4 * Kc + 1) * C₀ * (18 * lam * n) * n + 1 with hρ
  have hΔseed : 8 * Kc * C₀ ^ 2 * Δ ≤ Fintype.card (Fin n) := by
    rw [hcard]
    exact ar_seed hKc0 hn0.le hΔR L1
  have hρE : (4 * Kc + 1) * C₀ * Δ * Fintype.card (Fin n) < ρ := by
    rw [hcard, hρ]
    exact ar_rho hKc0 (by linarith) hn0.le hΔR
  have hlow₀ : ∀ X Y, X ≠ Y →
      η * ksz lab X * ksz lab Y + 6 * Fintype.card (Coord o) * ρ ≤ 2 * t₀ X Y := by
    intro X Y h
    have hlo := tsh_low o (fun A B => (t A B : ℝ)) s hsb X Y
    have hcc := ar_cc (Nat.cast_nonneg (ksz lab X)) (Nat.cast_nonneg (ksz lab Y)) (hkszn X)
      (hkszn Y)
    have key := ar_low hε hJc0 hlam0.le hlam1 hKc0 (by linarith) hn1 (by positivity) hcc
      (htl X Y h) hlo L2 L3 hεn
    have e : η * ksz lab X * ksz lab Y = ε / 2 * ((ksz lab X : ℝ) * ksz lab Y) := by
      rw [hη]; ring
    rw [e]
    exact key
  obtain ⟨μ, hμ, hμm⟩ := residual_seed_exact lab hk o hR1 hmBk h512 hmR hbal hδ hη0 hcls'
    (by rw [hcard]; linarith) t₀ hpair₀ hrow₀ P0 hP0all hP0disj hdeg0 hΔseed hρE hlow₀
  rw [hP0L] at hμ hμm
  -- H2, H3, H4 on `K_n − L`
  have hbig : BigRk lab L := bigRk_of_deg hdegL (fun X => by
    have : ((k + 4) * (Δ + 1) : ℝ) < ksz lab X :=
      ar_big (Nat.cast_nonneg k) hlam0.le hn0.le hΔR L6 hδnk (hcls X)
    exact_mod_cast this)
  obtain ⟨ob, hob, hobadj⟩ := exists_baseK hbig (⟨0, by
    have : (0 : ℝ) < n := hn0; exact_mod_cast this⟩ : Fin n)
  let nx : Fin k → Fin k := fun X => if X.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hnx : ∀ X, nx X ≠ X := by
    intro X h
    simp only [nx] at h
    split_ifs at h with h0
    · have := congrArg Fin.val h; simp at this; omega
    · have := congrArg Fin.val h; simp at this; omega
  have hsum : ∑ X, ksz lab X = n := by
    unfold ksz
    rw [← card_eq_sum_card_fiberwise (f := lab) (fun _ _ => mem_univ _), card_univ,
      Fintype.card_fin]
  have hn' : Even (Fintype.card (Fin n) - 1) := by
    rw [Fintype.card_fin]; obtain ⟨m', hm'⟩ := hodd; exact ⟨m', by omega⟩
  have H2 : IsPhysical (rHostK lab L) (bicF k) (edges (rHostK lab L)) :=
    residual_physicalK hbig hob hnx hobadj o P0 hP0all hP0disj hP0L.symm hn' heven
      (pair_of_div (ksz lab) hsum hdiv)
  obtain ⟨d10, d4⟩ := ar_D (Nat.cast_nonneg Δ) hn0.le hΔR L5 hδn20
  have hΔ4 : 4 * ((Δ : ℝ) + 1) ≤ δ * Fintype.card (Fin n) := by rw [hcard]; exact d4
  have hΔ10 : 10 * ((Δ : ℝ) + 1) ≤ δ * Fintype.card (Fin n) := by rw [hcard]; exact d10
  have H3 := commonNbr_mono (residual_H3K hdegL hcls' hΔ4) (ar_sq hδ hδ1)
  have H4 := residual_H4K hdegL hδ hcls' hΔ10
  -- Theorem T with monitors on the cycle coordinates
  let w : Coord o → Finset (Fin n) → ℝ := fun i Q => wXY lab i.1.1 i.1.2 Q
  have hν : (Fintype.card (Coord o) : ℝ) ≤ (Fintype.card (Fin n) : ℝ) ^ 2 := by
    rw [hcard]
    have h1 : Fintype.card (Coord o) ≤ Fintype.card (Fin k × Fin k) := Fintype.card_subtype_le _
    rw [Fintype.card_prod, Fintype.card_fin] at h1
    have : (Fintype.card (Coord o) : ℝ) ≤ (k : ℝ) * k := by exact_mod_cast h1
    exact ar_nu this (Nat.cast_nonneg k) hkn
  have hw : ∀ i Q, IsAllowed (rHostK lab L) (bicF k) Q → |w i Q| ≤ 1 := fun i Q _ => by
    simp only [w, wXY]; split_ifs <;> norm_num
  obtain ⟨D, hD, hstat⟩ := hT (rHostK lab L) μ
    (by rw [Fintype.card_fin]; exact le_of_max_le_left hn) hμ H2 H3 H4 (Coord o) w hν hw
  -- Attach the prescribed packing before making any switches.
  have hE := attach_prescribed lab LR Q hQall hQdisj hLRQ D hD
  have hDQ : Disjoint D Q := by
    apply Disjoint.symm
    apply packing_block_disjoint hQne
    rw [disjoint_biUnion_right]
    intro T hT
    exact ((disj_of_rHostK lab (hD.1 T hT)).mono_right subset_union_right).symm
  have hcount : ∀ X Y, kTypeCount lab (D ∪ Q) X Y =
      kTypeCount lab D X Y + kTypeCount lab Q X Y := by
    intro X Y
    unfold kTypeCount
    rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hDQ)]
  have hclose : ∀ i : Coord o,
      |(kTypeCount lab (D ∪ Q) i.1.1 i.1.2 : ℝ) -
        ((t i.1.1 i.1.2 : ℝ) - selectedBase lab o P S i + (g i : ℝ) / 2)| ≤ (g i : ℝ) / 4 := by
    intro i
    have h := hstat i
    have e1 : ∑ Q ∈ D, w i Q = (kTypeCount lab D i.1.1 i.1.2 : ℝ) := by
      simp only [w, wXY, kTypeCount]; rw [sum_boole]
    have e2 : ∑ Q ∈ allowed (rHostK lab L) (bicF k), μ Q * w i Q = t₀ i.1.1 i.1.2 := hμm i
    rw [e1, e2, hcard] at h
    have hc : t₀ i.1.1 i.1.2 = (t i.1.1 i.1.2 : ℝ) - selectedBase lab o P S i +
        (g i : ℝ) / 2 - kTypeCount lab Q i.1.1 i.1.2 := by
      rw [ht₀, tsh_coord]; simp only [hs]; ring
    rw [hc] at h
    have hclose := h.trans (hg i).2
    rw [hcount]
    push_cast
    convert hclose using 1 <;> congr 1 <;> ring
  obtain ⟨E, hEdec, hsub, hEt⟩ := exact_from_selected lab o hm8 P hPτ S (D ∪ Q) hE t htp htr hclose
  exact ⟨E, hEdec, subset_trans subset_union_right hsub, hEt⟩

end CDRBicolour.KBicolor
