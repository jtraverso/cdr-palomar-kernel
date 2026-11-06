/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.Theorem31Step
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Theorem 3.1 on `Fin n`: assembly of the induction -/

@[expose] public section

namespace Pseudorandom

namespace Patt

open Finset

variable {n q : ℕ} {ℓ : ℕ} {w : Finset (Fin n) → ℝ}

theorem two_mul_le_two_pow : ∀ ℓ : ℕ, 1 ≤ ℓ → 2 * ℓ ≤ 2 ^ ℓ
  | 0, h => absurd h (by omega)
  | 1, _ => by norm_num
  | ℓ + 2, _ => by
    have := two_mul_le_two_pow (ℓ + 1) (by omega)
    rw [pow_succ]; omega

/-- Under the good events, every count `cnt k (wt ℓ w i)` is at most `2 q^{ℓ-k-1} M`. -/
theorem cnt_wt_le_of_good (hq : 0 < q) (hw : ∀ e, 0 ≤ w e) {g M lam : ℝ} (hM : 0 < M)
    (hℓ : 1 ≤ ℓ) (hNB : NB ℓ w q g M) (α : ℕ → Fin q) (i : Fin n) (c : Fin n → Fin q)
    (hG : goodEv ℓ w α (nrm ℓ w ∅) M lam i c) {k : ℕ} (hk : k < ℓ) :
    cnt k (wt ℓ w i) α c ≤ 2 * ((q : ℝ) ^ (ℓ - k - 1) * M) := by
  rcases Nat.eq_zero_or_pos k with h0 | hk1
  · subst h0
    have h1 := cnt_le_nrm (ℓ := 0) (fun e => wt_nonneg (ℓ := ℓ) hw i e) α c
    have h2 := nrm_wt_le (ℓ := ℓ) (k := 0) (t := i) hw ∅
    have h3 := nrm_single_le hq hℓ hNB i
    have : (insert i (∅ : Finset (Fin n))) = {i} := rfl
    rw [this] at h2
    have : (0 : ℝ) ≤ (q : ℝ) ^ (ℓ - 0 - 1) * M := by positivity
    simp only [Nat.sub_zero] at this ⊢
    linarith
  · exact ((hG k hk1 hk).2 i rfl).le

theorem incB_le_of_good (hq : 0 < q) (hw : ∀ e, 0 ≤ w e) {g M lam : ℝ} (hM : 0 < M)
    (hℓ : 1 ≤ ℓ) (hNB : NB ℓ w q g M) (α : ℕ → Fin q) (i : Fin n) (c : Fin n → Fin q)
    (hG : goodEv ℓ w α (nrm ℓ w ∅) M lam i c) :
    incB ℓ w α i c ≤ 2 * ℓ * M := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [incB_eq]
  calc ∑ k ∈ range ℓ, (1 / (q : ℝ)) ^ (ℓ - 1 - k) * cnt k (wt ℓ w i) α c
      ≤ ∑ k ∈ range ℓ, (2 * M) := by
        refine sum_le_sum fun k hk => ?_
        rw [mem_range] at hk
        have h := cnt_wt_le_of_good hq hw hM hℓ hNB α i c hG hk
        have he : ℓ - 1 - k = ℓ - k - 1 := by omega
        rw [he]
        calc (1 / (q : ℝ)) ^ (ℓ - k - 1) * cnt k (wt ℓ w i) α c
            ≤ (1 / (q : ℝ)) ^ (ℓ - k - 1) * (2 * ((q : ℝ) ^ (ℓ - k - 1) * M)) :=
              mul_le_mul_of_nonneg_left h (by positivity)
          _ = 2 * M := by rw [one_div_pow]; field_simp
    _ = 2 * ℓ * M := by rw [sum_const, card_range, nsmul_eq_mul]; ring

theorem cnt_wle_le_of_good (hq : 0 < q) (hw : ∀ e, 0 ≤ w e) {M lam : ℝ} (hlam : 0 < lam)
    (α : ℕ → Fin q) (i : Fin n) (c : Fin n → Fin q)
    (hG : goodEv ℓ w α (nrm ℓ w ∅) M lam i c) {k : ℕ} (hk : k < ℓ) :
    cnt k (wle ℓ w (i + 1)) α c ≤
      nrm ℓ w ∅ * (1 / (q : ℝ)) ^ k + lam * (q : ℝ) ^ (ℓ - k) := by
  rcases Nat.eq_zero_or_pos k with h0 | hk1
  · subst h0
    have h1 := cnt_le_nrm (ℓ := 0) (fun e => wle_nonneg (ℓ := ℓ) hw (i + 1) e) α c
    have h2 := nrm_wle_le (ℓ := ℓ) (k := 0) (t := i + 1) hw ∅
    have : (0 : ℝ) ≤ lam * (q : ℝ) ^ (ℓ - 0) := by positivity
    simp only [pow_zero, mul_one]
    linarith
  · exact (hG k hk1 hk).1.le

theorem acc_le_of_good (hq : 0 < q) (hw : ∀ e, 0 ≤ w e) {M lam : ℝ} (hlam : 0 < lam)
    (α : ℕ → Fin q) (i : Fin n) (c : Fin n → Fin q)
    (hG : goodEv ℓ w α (nrm ℓ w ∅) M lam i c) :
    ∑ j : Fin n with j ≤ i, condAbsInc (unif (Fin n) q) (Xp ℓ w α) j c ≤
      2 * ℓ * (nrm ℓ w ∅ * (1 / (q : ℝ)) ^ ℓ + lam) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hfil : (univ.filter fun j : Fin n => j ≤ i) =
      univ.filter (fun s : Fin n => (s : ℕ) < (i : ℕ) + 1) := by
    ext j; simp only [mem_filter, mem_univ, true_and, Fin.le_def]; omega
  calc ∑ j : Fin n with j ≤ i, condAbsInc (unif (Fin n) q) (Xp ℓ w α) j c
      ≤ ∑ j : Fin n with j ≤ i, 2 / q * incB ℓ w α j c :=
        sum_le_sum fun j _ => condAbsInc_Xp_le hq hw α j c
    _ = ∑ k ∈ range ℓ, 2 / q * (1 / (q : ℝ)) ^ (ℓ - 1 - k) *
          cnt k (wle ℓ w (i + 1)) α c := by
        simp_rw [incB_eq, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        unfold wle
        rw [cnt_sum, mul_sum, hfil]
        refine sum_congr rfl fun j _ => by ring
    _ ≤ ∑ k ∈ range ℓ, 2 * (nrm ℓ w ∅ * (1 / (q : ℝ)) ^ ℓ + lam) := by
        refine sum_le_sum fun k hk => ?_
        rw [mem_range] at hk
        have h := cnt_wle_le_of_good hq hw hlam α i c hG hk
        calc 2 / (q : ℝ) * (1 / (q : ℝ)) ^ (ℓ - 1 - k) * cnt k (wle ℓ w (i + 1)) α c
            ≤ 2 / (q : ℝ) * (1 / (q : ℝ)) ^ (ℓ - 1 - k) *
                (nrm ℓ w ∅ * (1 / (q : ℝ)) ^ k + lam * (q : ℝ) ^ (ℓ - k)) :=
              mul_le_mul_of_nonneg_left h (by positivity)
          _ = 2 * (nrm ℓ w ∅ * (1 / (q : ℝ)) ^ ℓ + lam) := by
              have e1 : (q : ℝ) ^ ℓ = (q : ℝ) ^ (ℓ - 1 - k) * (q : ℝ) ^ k * q := by
                rw [← pow_add, ← pow_succ]; congr 1; omega
              have e2 : (q : ℝ) ^ (ℓ - k) = (q : ℝ) ^ (ℓ - 1 - k) * q := by
                rw [← pow_succ]; congr 1; omega
              rw [one_div_pow, one_div_pow, one_div_pow, e1, e2]
              field_simp
    _ = 2 * ℓ * (nrm ℓ w ∅ * (1 / (q : ℝ)) ^ ℓ + lam) := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- If `M ≤ 0` the weight function vanishes on all `ℓ`-sets. -/
theorem w_eq_zero_of_M_nonpos (hq : 0 < q) (hw : ∀ e, 0 ≤ w e) {g M : ℝ} (hM : M ≤ 0)
    (hℓ : 1 ≤ ℓ) (hNB : NB ℓ w q g M) : ∀ e ∈ powersetCard ℓ univ, w e = 0 := by
  intro e he
  have hne : e.Nonempty := by
    rw [mem_powersetCard] at he
    rw [← card_pos, he.2]; omega
  obtain ⟨v, hv⟩ := hne
  have h1 := nrm_single_le hq hℓ hNB v
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h2 : (q : ℝ) ^ (ℓ - 1) * M ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hM
  have h3 : w e ≤ nrm ℓ w {v} := by
    unfold nrm
    exact single_le_sum (f := w) (fun e _ => hw e)
      (mem_filter.mpr ⟨he, singleton_subset_iff.mpr hv⟩)
  linarith [hw e]

/-- **The inductive step of Theorem 3.1.** -/
theorem conc31_step (hq : 0 < q) {g : ℝ} (hℓ : 1 ≤ ℓ)
    (hg : 24 * (ℓ : ℝ) ^ 3 * (ℓ + 1 + Real.log n) ≤ g)
    (IH : ∀ k, 1 ≤ k → k < ℓ → Conc31 n q g k) : Conc31 n q g ℓ := by
  classical
  intro w hw α M hNB lam hlam
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hP := unif_isPMF (ι := Fin n) q hq
  have hL1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hg0 : 0 < g := by
    have : 0 < 24 * (ℓ : ℝ) ^ 3 * (ℓ + 1 + Real.log n) := by positivity
    linarith
  set N := nrm ℓ w ∅ with hN
  set E := N * (1 / (q : ℝ)) ^ ℓ with hE
  have hN0 : 0 ≤ N := nrm_nonneg hw ∅
  have hE0 : 0 ≤ E := by positivity
  set e1 := Real.exp (-(lam ^ 2 / (12 * ℓ ^ 2 * M * (lam + E)))) with he1
  set e2 := Real.exp (-(g / (24 * ℓ ^ 2))) with he2
  have he10 : 0 ≤ e1 := (Real.exp_pos _).le
  have he20 : 0 ≤ e2 := (Real.exp_pos _).le
  -- the degenerate case
  rcases le_or_gt M 0 with hM | hM
  · have hz := w_eq_zero_of_M_nonpos hq hw hM hℓ hNB
    have hcnt : ∀ c, cnt ℓ w α c = 0 := fun c =>
      sum_eq_zero fun e he => by rw [hz e he, zero_mul]
    have hN' : N = 0 := by
      rw [hN, nrm_empty_eq]; exact sum_eq_zero hz
    have : pProb (unif (Fin n) q) (fun c => lam ≤ |cnt ℓ w α c - N * (1 / (q : ℝ)) ^ ℓ|) = 0 := by
      unfold pProb pE
      refine sum_eq_zero fun c _ => ?_
      simp only [hcnt c, hN', zero_mul, sub_zero, abs_zero, not_le.mpr hlam, if_false, mul_zero]
    rw [this]; positivity
  -- the main case
  set X := Xp ℓ w α with hX
  have hXm := Xp_mart hq ℓ w α
  set G := goodEv ℓ w α N M lam with hG
  have hGa : ∀ k, Adapted k (G k) := fun k => goodEv_adapted α N M lam k
  set C := 2 * ℓ * M with hC
  set s := 2 * ℓ * (E + lam) with hs
  have hC0 : 0 < C := by positivity
  have hs0 : 0 < s := by positivity
  have hfr := freedman_two_sided hP hXm hGa C s lam hC0 hs0 hlam
    (fun i c hal a _ => (abs_Xp_inc_le hq hw α i c a).trans
      (incB_le_of_good hq hw hM hℓ hNB α i c (hal i le_rfl)))
    (fun i c hal => acc_le_of_good hq hw hlam α i c (hal i le_rfl))
  have hX0 : ∀ c, X 0 c = E := fun c => by
    rw [hX, Xp_zero, hE, hN, nrm_empty_eq, sum_mul]
  have hXn : ∀ c, X n c = cnt ℓ w α c := fun c => Xp_n ℓ w α c
  -- the bad event
  have hbad : pProb (unif (Fin n) q) (fun c => ∃ i : Fin n, ¬ G i c) ≤ (2 ^ ℓ - 2) * e1 + e2 := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      have : pProb (unif (Fin 0) q) (fun c => ∃ i : Fin 0, ¬ G i c) = 0 := by
        unfold pProb pE; refine sum_eq_zero fun c _ => ?_; simp
      rw [this]
      have : (2 : ℝ) ≤ 2 ^ ℓ := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
      nlinarith
    -- union bound
    set A : ℕ → (Fin n → Fin q) → Prop := fun k c =>
      N * (1 / (q : ℝ)) ^ k + lam * (q : ℝ) ^ (ℓ - k) ≤ cnt k (wle ℓ w n) α c
    set B : ℕ → Fin n → (Fin n → Fin q) → Prop := fun k s c =>
      2 * ((q : ℝ) ^ (ℓ - k - 1) * M) ≤ cnt k (wt ℓ w s) α c
    have hincl : ∀ c, (∃ i : Fin n, ¬ G i c) →
        ∃ k ∈ Ico 1 ℓ, (A k c ∨ ∃ s ∈ (univ : Finset (Fin n)), B k s c) := by
      rintro c ⟨i, hi⟩
      simp only [hG, goodEv, not_forall, not_and_or, not_lt] at hi
      obtain ⟨k, hk1, hk, h⟩ := hi
      refine ⟨k, mem_Ico.mpr ⟨hk1, hk⟩, ?_⟩
      rcases h with h | h
      · left
        refine h.trans (cnt_mono (fun T => wle_mono hw (by omega) T) α c)
      · right
        obtain ⟨s, hs, h⟩ := h
        exact ⟨s, mem_univ _, h⟩
    have hk_bound : ∀ k ∈ Ico 1 ℓ, pProb (unif (Fin n) q)
        (fun c => A k c ∨ ∃ s ∈ (univ : Finset (Fin n)), B k s c) ≤
        2 ^ k * e1 + (n * (2 ^ k + 2)) * Real.exp (-(g / (24 * k ^ 2))) := by
      intro k hk
      rw [mem_Ico] at hk
      refine (pProb_or_le hP _ _).trans ?_
      have ha := tail_wle hq hw hg0 hM hlam hNB hk.1 hk.2 (IH k hk.1 hk.2) α n
      have hb := pProb_exists_le hP (univ : Finset (Fin n)) (B k)
      have hb' : ∑ s : Fin n, pProb (unif (Fin n) q) (B k s) ≤
          n * ((2 ^ k + 1) * Real.exp (-(g / (24 * k ^ 2)))) := by
        calc ∑ s : Fin n, pProb (unif (Fin n) q) (B k s)
            ≤ ∑ s : Fin n, (2 ^ k + 1) * Real.exp (-(g / (24 * k ^ 2))) :=
              sum_le_sum fun s _ => tail_wt hq hw hg0 hM hNB hk.1 hk.2 (IH k hk.1 hk.2) α s
          _ = n * ((2 ^ k + 1) * Real.exp (-(g / (24 * k ^ 2)))) := by
              rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hx : 0 ≤ Real.exp (-(g / (24 * k ^ 2))) := (Real.exp_pos _).le
      have : pProb (unif (Fin n) q) (A k) ≤ 2 ^ k * e1 + Real.exp (-(g / (24 * k ^ 2))) := ha
      nlinarith
    refine (pProb_mono hP hincl).trans ((pProb_exists_le hP _ _).trans ?_)
    refine (sum_le_sum hk_bound).trans ?_
    rw [sum_add_distrib, ← sum_mul, sum_Ico_two_pow ℓ hℓ]
    refine add_le_add le_rfl ?_
    rcases Nat.lt_or_ge ℓ 2 with hl2 | hl2
    · have : Ico 1 ℓ = ∅ := by ext k; simp only [mem_Ico, notMem_empty, iff_false]; omega
      rw [this, sum_empty]; exact he20
    · have hL2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hl2
      set e3 := Real.exp (-(g / (24 * ((ℓ : ℝ) - 1) ^ 2))) with he3
      have hk3 : ∀ k ∈ Ico 1 ℓ, (n : ℝ) * (2 ^ k + 2) * Real.exp (-(g / (24 * k ^ 2))) ≤
          (n : ℝ) * (2 ^ k + 2) * e3 := by
        intro k hk
        rw [mem_Ico] at hk
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff]
        have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
        have hkl : (k : ℝ) ≤ ℓ - 1 := by
          have : k + 1 ≤ ℓ := hk.2
          have : ((k + 1 : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast this
          push_cast at this; linarith
        apply div_le_div_of_nonneg_left hg0.le (by positivity)
        have := pow_le_pow_left₀ (by positivity) hkl 2
        linarith
      refine (sum_le_sum hk3).trans ?_
      rw [← sum_mul, ← mul_sum, sum_add_distrib, sum_Ico_two_pow ℓ hℓ, sum_const,
        Nat.card_Ico, nsmul_eq_mul]
      have hnum := union_numeric hl2 hn1 hg
      have hsum : (2 : ℝ) ^ ℓ - 2 + ((ℓ - 1 : ℕ) : ℝ) * 2 ≤ 2 ^ (ℓ + 1) := by
        rw [Nat.cast_sub hℓ]
        have : 2 * (ℓ : ℝ) ≤ 2 ^ ℓ := by
          exact_mod_cast two_mul_le_two_pow ℓ hℓ
        rw [pow_succ]; push_cast; linarith
      have he30 : 0 ≤ e3 := (Real.exp_pos _).le
      have hn0 : (0 : ℝ) ≤ n := by positivity
      calc (n : ℝ) * (2 ^ ℓ - 2 + ((ℓ - 1 : ℕ) : ℝ) * 2) * e3
          ≤ (n : ℝ) * 2 ^ (ℓ + 1) * e3 := by gcongr
        _ = 2 ^ (ℓ + 1) * n * e3 := by ring
        _ ≤ e2 := hnum
  -- comparing the Freedman exponent
  have hfr_exp : Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) ≤ e1 := by
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    rw [hC, hs]
    have : 4 * (ℓ : ℝ) * M * (lam + 2 * ℓ * (E + lam)) ≤ 12 * ℓ ^ 2 * M * (lam + E) := by
      have h1 : (4 : ℝ) * ℓ * (lam + 2 * ℓ * (E + lam)) ≤ 12 * ℓ ^ 2 * (lam + E) := by
        nlinarith
      nlinarith
    linarith
  -- assembling
  calc pProb (unif (Fin n) q) (fun c => lam ≤ |cnt ℓ w α c - N * (1 / (q : ℝ)) ^ ℓ|)
      ≤ pProb (unif (Fin n) q) (fun c => (lam ≤ |X n c - X 0 c| ∧ ∀ i : Fin n, G i c) ∨
          ∃ i : Fin n, ¬ G i c) := by
        refine pProb_mono hP fun c hc => ?_
        by_cases h : ∀ i : Fin n, G i c
        · left; refine ⟨?_, h⟩; rw [hXn, hX0]; exact hc
        · right; push_neg at h; exact h
    _ ≤ 2 * Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) + ((2 ^ ℓ - 2) * e1 + e2) :=
        (pProb_or_le hP _ _).trans (add_le_add hfr hbad)
    _ ≤ 2 ^ ℓ * e1 + e2 := by nlinarith

/-- **Theorem 3.1 on `Fin n`** (all levels). -/
theorem conc31 (hq : 0 < q) {g : ℝ} :
    ∀ ℓ : ℕ, 1 ≤ ℓ → 24 * (ℓ : ℝ) ^ 3 * (ℓ + 1 + Real.log n) ≤ g → Conc31 n q g ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro hℓ hg
    apply conc31_step hq hℓ hg
    intro k hk1 hk
    apply ih k hk hk1
    have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hkl : (k : ℝ) ≤ ℓ := by exact_mod_cast hk.le
    have hk0 : (0 : ℝ) ≤ k := by positivity
    calc 24 * (k : ℝ) ^ 3 * (k + 1 + Real.log n) ≤ 24 * (ℓ : ℝ) ^ 3 * (ℓ + 1 + Real.log n) := by
          gcongr
      _ ≤ g := hg

end Patt

end Pseudorandom
