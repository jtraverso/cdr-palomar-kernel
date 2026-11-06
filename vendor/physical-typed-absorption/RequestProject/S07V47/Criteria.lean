/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V46.Alloc
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-!
# V47 §1 — prefix-capacity criteria for EARLY STOPPING and the relaxed final prefix

V46 `prefix_capacity` uses the localized bounds `b ℓ ≤ θ S ℓ` for `ℓ < J`, the full bound
`b J ≤ τ'` at the last step, and the final premise `1 + τ' ≤ S J`.  Here:

* `prefix_capacity_local` : if EVERY step `ℓ ≤ J` has a localized bound `b ℓ ≤ θ S ℓ` (early stop:
  the last step pays into a final subgroup that is already `⊥`, through a localized monitor),
  then `∑_{k ≤ t} a k ≤ P S t` for all `t ≤ J` with NO quadratic / full-monitor term at all.
* `prefix_capacity_relaxed` : the final premise can be relaxed to `1 + τ' ≤ 2 S J` with the SAME
  colour count `P ≥ 2Γ`.  The point is that the full budget `τ'` enters only the last step and is
  therefore not compounded by the recurrence factor `(1 + AM)`, and the factor `L+1` of `Γ`
  absorbs the remaining terms:
  `∑_{k ≤ J} a k ≤ (1+AM) G_{J-1} (1 + S) + A (1 + τ') ≤ A J (1+AM)^L · 2S + A (1+AM)^L · 2S ≤ 2Γ S`.
* `strata_allocation_of_cap` : V46 `strata_allocation` with the numeric criterion replaced by an
  ARBITRARY prefix-capacity property of the recurrence (so that the criteria above, and the
  original V46 one, all plug into the same exact chain/pooling/splitting machinery).
-/

@[expose] public section

namespace S07V47

open Finset S07V46

lemma geomG_le_self (A M t : ℕ) : geomG A M t ≤ (gammaL A M t : ℝ) :=
  geomG_le_gammaL le_rfl

lemma sum_range_mono_nat (m : ℕ → ℕ) {s s' : ℕ} (h : s ≤ s') :
    ∑ i ∈ range (s + 1), (m i : ℝ) ≤ ∑ i ∈ range (s' + 1), (m i : ℝ) :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun _ _ _ => Nat.cast_nonneg _

lemma one_le_prefix (m : ℕ → ℕ) (hm0 : 1 ≤ m 0) (t : ℕ) :
    (1 : ℝ) ≤ ∑ i ∈ range (t + 1), (m i : ℝ) :=
  calc (1 : ℝ) ≤ m 0 := by exact_mod_cast hm0
    _ = ∑ i ∈ range (0 + 1), (m i : ℝ) := by simp
    _ ≤ _ := sum_range_mono_nat m (Nat.zero_le t)

/-- **Early-stop criterion: all steps localized, no full budget.** -/
theorem prefix_capacity_local (A M P L J : ℕ) (hJL : J ≤ L) (m : ℕ → ℕ) (a b : ℕ → ℝ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hrec : ∀ ℓ ≤ J, a ℓ ≤ A * (1 + b ℓ + M * ∑ k ∈ range ℓ, a k))
    (hloc : ∀ ℓ ≤ J, b ℓ ≤ θ * ∑ i ∈ range (ℓ + 1), (m i : ℝ))
    (hP : 2 * gammaL A M L ≤ P) (hm0 : 1 ≤ m 0) :
    ∀ t ≤ J, ∑ k ∈ range (t + 1), a k ≤ P * ∑ i ∈ range (t + 1), (m i : ℝ) := by
  intro t ht
  have hS1 := one_le_prefix m hm0 t
  set St := ∑ i ∈ range (t + 1), (m i : ℝ)
  have hG := geomG_le_gammaL (A := A) (M := M) (ht.trans hJL)
  have hG0 := geomG_nonneg A M t
  have hP' : (2 : ℝ) * gammaL A M L ≤ P := by exact_mod_cast hP
  have hb : ∀ ℓ ≤ t, b ℓ ≤ θ * St := fun ℓ hℓ =>
    (hloc ℓ (by omega)).trans (mul_le_mul_of_nonneg_left (sum_range_mono_nat m hℓ) hθ0)
  have hc := cum_bound A M a b (θ * St) t (fun ℓ hℓ => hrec ℓ (by omega)) hb
  calc ∑ k ∈ range (t + 1), a k ≤ geomG A M t * (1 + θ * St) := hc
    _ ≤ gammaL A M L * (St + St) := by
        refine mul_le_mul hG (by nlinarith) (by positivity) (by positivity)
    _ = 2 * gammaL A M L * St := by ring
    _ ≤ P * St := by gcongr

/-- **Relaxed final criterion `1 + τ' ≤ 2 S_J` with the same colour count `P ≥ 2Γ`.** -/
theorem prefix_capacity_relaxed (A M P L J : ℕ) (hJL : J ≤ L) (m : ℕ → ℕ) (a b : ℕ → ℝ)
    {θ τ' : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hrec : ∀ ℓ ≤ J, a ℓ ≤ A * (1 + b ℓ + M * ∑ k ∈ range ℓ, a k))
    (hloc : ∀ ℓ < J, b ℓ ≤ θ * ∑ i ∈ range (ℓ + 1), (m i : ℝ))
    (hfull : b J ≤ τ')
    (hP : 2 * gammaL A M L ≤ P) (hm0 : 1 ≤ m 0)
    (hSJ : 1 + τ' ≤ 2 * ∑ i ∈ range (J + 1), (m i : ℝ)) :
    ∀ t ≤ J, ∑ k ∈ range (t + 1), a k ≤ P * ∑ i ∈ range (t + 1), (m i : ℝ) := by
  intro t ht
  rcases lt_or_eq_of_le ht with hlt | heq
  · -- strictly before the last step: localized bounds only
    have := prefix_capacity_local A M P L t (by omega) m a b hθ0 hθ1
      (fun ℓ hℓ => hrec ℓ (by omega)) (fun ℓ hℓ => hloc ℓ (by omega)) hP hm0
    exact this t le_rfl
  · subst heq
    have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have h1 : (1 : ℝ) ≤ 1 + A * M := by nlinarith
    have hX1 : (1 : ℝ) ≤ (1 + A * M) ^ L := one_le_pow₀ h1
    have hP' : (2 : ℝ) * gammaL A M L ≤ P := by exact_mod_cast hP
    have hS1 := one_le_prefix m hm0 t
    set St := ∑ i ∈ range (t + 1), (m i : ℝ) with hSt
    have hgam : (gammaL A M L : ℝ) = A * (L + 1) * (1 + A * M) ^ L := by
      unfold gammaL; push_cast; ring
    cases t with
    | zero =>
      have h0 := hrec 0 le_rfl
      simp only [range_zero, sum_empty, mul_zero, add_zero] at h0
      have hAΓ : (A : ℝ) ≤ gammaL A M L := by
        rw [hgam]
        have : (1 : ℝ) ≤ (L + 1) * (1 + A * M) ^ L := by
          nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
        nlinarith
      have hS0 : (0 : ℝ) ≤ St := by linarith
      have hb0 : b 0 ≤ τ' := hfull
      calc ∑ k ∈ range (0 + 1), a k = a 0 := by simp
        _ ≤ A * (1 + b 0) := h0
        _ ≤ A * (1 + τ') := by gcongr
        _ ≤ A * (2 * St) := by gcongr
        _ ≤ gammaL A M L * (2 * St) := by gcongr
        _ = 2 * gammaL A M L * St := by ring
        _ ≤ P * St := by gcongr
    | succ j =>
      set Sj := ∑ i ∈ range (j + 1), (m i : ℝ) with hSj
      have hSjSt : Sj ≤ St := sum_range_mono_nat m (Nat.le_succ j)
      have hSj0 : 0 ≤ Sj := sum_nonneg fun _ _ => Nat.cast_nonneg _
      have hθSj : θ * Sj ≤ St := by nlinarith
      have hbj : ∀ ℓ ≤ j, b ℓ ≤ θ * Sj := fun ℓ hℓ =>
        (hloc ℓ (by omega)).trans (mul_le_mul_of_nonneg_left (sum_range_mono_nat m hℓ) hθ0)
      have hCj := cum_bound A M a b (θ * Sj) j (fun ℓ hℓ => hrec ℓ (by omega)) hbj
      set Cj := ∑ k ∈ range (j + 1), a k with hCjdef
      have hGj : geomG A M j ≤ A * (j + 1) * (1 + A * M) ^ j := by
        have := geomG_le_self A M j; unfold gammaL at this; push_cast at this; exact this
      have hG0 := geomG_nonneg A M j
      have hlast := hrec (j + 1) le_rfl
      have hbJ : b (j + 1) ≤ τ' := hfull
      have hCj' : Cj ≤ geomG A M j * (1 + St) :=
        hCj.trans (mul_le_mul_of_nonneg_left (by linarith) hG0)
      have hsplit : ∑ k ∈ range (j + 1 + 1), a k = Cj + a (j + 1) := by
        rw [sum_range_succ]
      rw [hsplit]
      have hsum : Cj + a (j + 1) ≤ (1 + A * M) * Cj + A * (1 + τ') := by
        have : a (j + 1) ≤ A * (1 + τ' + M * Cj) :=
          hlast.trans (by gcongr)
        nlinarith
      have hpow : ((1 : ℝ) + A * M) ^ (j + 1) ≤ (1 + A * M) ^ L := pow_le_pow_right₀ h1 hJL
      have hGG : (1 + A * M) * geomG A M j ≤ A * (j + 1) * (1 + A * M) ^ L := by
        calc (1 + A * M) * geomG A M j ≤ (1 + A * M) * (A * (j + 1) * (1 + A * M) ^ j) := by
              gcongr
          _ = A * (j + 1) * (1 + A * M) ^ (j + 1) := by ring
          _ ≤ A * (j + 1) * (1 + A * M) ^ L := by gcongr
      have hX : (A : ℝ) * (1 + τ') ≤ A * (1 + A * M) ^ L * (2 * St) := by
        have : (1 + τ') ≤ 2 * St := hSJ
        calc (A : ℝ) * (1 + τ') ≤ A * (2 * St) := by gcongr
          _ = A * 1 * (2 * St) := by ring
          _ ≤ A * (1 + A * M) ^ L * (2 * St) := by gcongr
      have hJ1 : ((j : ℝ) + 1) + 1 ≤ L + 1 := by
        have : ((j + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hJL
        push_cast at this; linarith
      calc Cj + a (j + 1) ≤ (1 + A * M) * Cj + A * (1 + τ') := hsum
        _ ≤ (1 + A * M) * (geomG A M j * (1 + St)) + A * (1 + τ') := by gcongr
        _ = ((1 + A * M) * geomG A M j) * (1 + St) + A * (1 + τ') := by ring
        _ ≤ (A * (j + 1) * (1 + A * M) ^ L) * (2 * St) + A * (1 + A * M) ^ L * (2 * St) := by
            gcongr
            · linarith
        _ = 2 * (A * ((j + 1) + 1) * (1 + A * M) ^ L) * St := by ring
        _ ≤ 2 * (A * (L + 1) * (1 + A * M) ^ L) * St := by
            gcongr
        _ = 2 * gammaL A M L * St := by rw [hgam]
        _ ≤ P * St := by gcongr

/-- the V46 final premise implies the relaxed one -/
lemma relaxed_of_V46 {τ' S : ℝ} (hS : 0 ≤ S) (h : 1 + τ' ≤ S) : 1 + τ' ≤ 2 * S := by linarith

variable {Q C : Type*} [AddCommGroup Q] [Fintype C]

/-- **Global capacitated allocation along the strata, for ANY prefix-capacity criterion.**
Same mechanism as V46 `strata_allocation` (exact chain + prefix pooling + capacitated splitting);
the numeric criterion is replaced by the property `hcap` of every solution of the recurrence. -/
theorem strata_allocation_of_cap {g : C → Q} {G : AddSubgroup Q} {Ks Kc : ℕ → AddSubgroup Q}
    {μ : ℕ → Q → ℝ} {A M P J : ℕ}
    (hanti : ∀ i j, i ≤ j → Ks j ≤ Ks i)
    (hKc : ∀ ℓ ≤ J, Kc ℓ = Ks ℓ) (hbot : Kc (J + 1) = ⊥)
    (hS : StepPay g G Kc μ A M J) (m : ℕ → ℕ)
    (x : Q) (hxG : x ∈ G) (hx : x ∈ Ks 0)
    (hcap : ∀ a : ℕ → ℝ, (∀ ℓ ≤ J, a ℓ ≤ A * (1 + μ ℓ x + M * ∑ k ∈ range ℓ, a k)) →
      ∀ t ≤ J, ∑ k ∈ range (t + 1), a k ≤ P * ∑ i ∈ range (t + 1), (m i : ℝ)) :
    ∃ z : ℕ → Fin P → C → ℤ, (∀ i p c, z i p c ≠ 0 → i ≤ J ∧ g c ∈ Ks i) ∧
      (∀ i p c, (z i p c).natAbs ≤ m i) ∧
      x + ∑ i ∈ range (J + 1), ∑ p, wcls g (z i p) = 0 := by
  classical
  obtain ⟨u, hu, hux, hurec⟩ := chain_pay hS x hxG (by rw [hKc 0 (Nat.zero_le _)]; exact hx)
  rw [hbot, AddSubgroup.mem_bot] at hux
  have hcap' := hcap (fun ℓ => (wcost (u ℓ) : ℝ)) hurec
  have hus : ∀ ℓ c, u ℓ c ≠ 0 → ℓ ≤ J ∧ g c ∈ Ks ℓ := fun ℓ c h =>
    ⟨(hu ℓ c h).1, by rw [← hKc ℓ (hu ℓ c h).1]; exact (hu ℓ c h).2⟩
  set w : C → ℤ := fun c => ∑ ℓ ∈ range (J + 1), u ℓ c with hw
  have hent : ∀ c, ∃ zc : ℕ → Fin P → ℤ, (∀ i p, zc i p ≠ 0 → i ≤ J ∧ g c ∈ Ks i) ∧
      (∀ i p, (zc i p).natAbs ≤ m i) ∧ ∑ i ∈ range (J + 1), ∑ p, zc i p = w c := by
    intro c
    by_cases hex : ∃ ℓ ≤ J, u ℓ c ≠ 0
    · set t := Nat.findGreatest (fun ℓ => g c ∈ Ks ℓ) J with ht
      obtain ⟨ℓ0, hℓ0J, hℓ0⟩ := hex
      have htJ : t ≤ J := Nat.findGreatest_le J
      have hgt : g c ∈ Ks t := Nat.findGreatest_spec (P := fun ℓ => g c ∈ Ks ℓ) hℓ0J
        (hus ℓ0 c hℓ0).2
      have hle_t : ∀ ℓ, u ℓ c ≠ 0 → ℓ ≤ t := fun ℓ h =>
        Nat.le_findGreatest (hus ℓ c h).1 (hus ℓ c h).2
      have hwt : w c = ∑ ℓ ∈ range (t + 1), u ℓ c := by
        rw [hw]
        refine (sum_subset (range_subset_range.2 (by omega)) fun ℓ hℓ hℓt => ?_).symm
        by_contra h
        have := hle_t ℓ h
        simp at hℓt; omega
      have habs : (w c).natAbs ≤ ∑ ℓ ∈ range (t + 1), wcost (u ℓ) := by
        rw [hwt]
        refine (Int.natAbs_sum_le _ _).trans (sum_le_sum fun ℓ _ => ?_)
        exact single_le_sum (f := fun c => (u ℓ c).natAbs) (fun _ _ => Nat.zero_le _)
          (mem_univ c)
      have hP' : (w c).natAbs ≤ P * ∑ i ∈ range (t + 1), m i := by
        have h1 := hcap' t htJ
        have h2 : (((w c).natAbs : ℕ) : ℝ) ≤ ((P * ∑ i ∈ range (t + 1), m i : ℕ) : ℝ) := by
          push_cast
          calc ((w c).natAbs : ℝ) ≤ ((∑ ℓ ∈ range (t + 1), wcost (u ℓ) : ℕ) : ℝ) := by
                exact_mod_cast habs
            _ = ∑ ℓ ∈ range (t + 1), (wcost (u ℓ) : ℝ) := by push_cast; rfl
            _ ≤ P * ∑ i ∈ range (t + 1), (m i : ℝ) := h1
        exact_mod_cast h2
      obtain ⟨zc, hzc1, hzc0, hzcs⟩ := strata_split P m t (w c) hP'
      refine ⟨zc, fun i p h => ?_, hzc1, ?_⟩
      · have hit : i ≤ t := by
          by_contra hh; exact h (hzc0 i p (by omega))
        exact ⟨hit.trans htJ, hanti i t hit hgt⟩
      · rw [← hzcs]
        refine (sum_subset (range_subset_range.2 (by omega)) fun i hi hit => ?_).symm
        simp at hit
        exact sum_eq_zero fun p _ => hzc0 i p (by omega)
    · push_neg at hex
      refine ⟨fun _ _ => 0, fun _ _ h => absurd rfl h, fun _ _ => Nat.zero_le _, ?_⟩
      simp only [sum_const_zero, hw]
      exact (sum_eq_zero fun ℓ hℓ => hex ℓ (by simp at hℓ; omega)).symm
  choose zc hzc1 hzc2 hzc3 using hent
  refine ⟨fun i p c => zc c i p, fun i p c h => hzc1 c i p h, fun i p c => hzc2 c i p, ?_⟩
  have htot : ∑ i ∈ range (J + 1), ∑ p, wcls g (fun c => zc c i p) =
      ∑ ℓ ∈ range (J + 1), wcls g (u ℓ) := by
    rw [← wcls_sum]
    have : ∀ i ∈ range (J + 1), ∑ p, wcls g (fun c => zc c i p) =
        wcls g (fun c => ∑ p, zc c i p) := fun i _ => (wcls_sum g univ _).symm
    rw [sum_congr rfl this, ← wcls_sum]
    unfold wcls
    refine sum_congr rfl fun c _ => ?_
    dsimp only
    rw [hzc3 c]
  rw [htot]; exact hux

end S07V47
