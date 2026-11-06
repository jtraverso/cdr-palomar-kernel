/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V46.Split
public import RequestProject.S07V46.Chain
public import RequestProject.S07V46.Capacity
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-!
# V46 §4 — global capacitated integer allocation (abstract form, exact cancellation)

Setting: `g : C → Q` a finite catalog, `G ≤ Q` containing every `g c`, an ANTITONE family of
subgroups `Ks 0 ⊇ Ks 1 ⊇ …` (the actual `K_{Z_j}` of the strata), stratum lengths `m j`, `P`
colours.  The chain used for payment is `Kc ℓ = Ks ℓ` (`ℓ ≤ J`), `Kc (J+1) = ⊥`.

`strata_allocation` : under `StepPay` (one-step payment with monitors), localized step bounds
`μ ℓ x ≤ θ S ℓ` (`ℓ < J`), the full bound `μ J x ≤ τ'`, and the numeric criterion of
`prefix_capacity`, there is an occurrence word `z : ℕ → Fin P → C → ℤ` with

* `z i p c ≠ 0 → i ≤ J ∧ g c ∈ Ks i` (each unit is selected in a stratum where its entry is active);
* `|z i p c| ≤ m i` (the exact per-(entry, sign, colour) capacity of stratum `i`);
* `x + ∑_{i ≤ J} ∑_p [z i p] = 0` EXACTLY (torsion included).

Mechanism: the exact chain (`chain_pay`) produces step words `u ℓ`; the net word `w c = ∑ u ℓ c`
is POOLED over prefixes: entry `c` is active in every stratum `i ≤ top c` (`top c` the last
`ℓ ≤ J` with `g c ∈ Ks ℓ`), and only steps `ℓ ≤ top c` use `c`, so
`|w c| ≤ ∑_{ℓ ≤ top c} |u ℓ| ≤ P · S (top c)` (`prefix_capacity`); `strata_split` then distributes
`w c` over the slots (stratum `i ≤ top c`, colour `p`).  Several strata and several colours are
used; no single stratum is assumed to pay.
-/

@[expose] public section

namespace S07V46

open Finset

variable {Q C : Type*} [AddCommGroup Q] [Fintype C]

/-- **Global capacitated integer allocation along the strata (exact).** -/
theorem strata_allocation {g : C → Q} {G : AddSubgroup Q} {Ks Kc : ℕ → AddSubgroup Q}
    {μ : ℕ → Q → ℝ} {A M P L J : ℕ} (hJL : J ≤ L)
    (hanti : ∀ i j, i ≤ j → Ks j ≤ Ks i)
    (hKc : ∀ ℓ ≤ J, Kc ℓ = Ks ℓ) (hbot : Kc (J + 1) = ⊥)
    (hS : StepPay g G Kc μ A M J) (m : ℕ → ℕ) {θ τ' : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hτ : 0 ≤ τ') (hP : 2 * gammaL A M L ≤ P) (hm0 : 1 ≤ m 0)
    (hSJ : 1 + τ' ≤ ∑ i ∈ range (J + 1), (m i : ℝ))
    (x : Q) (hxG : x ∈ G) (hx : x ∈ Ks 0)
    (hloc : ∀ ℓ < J, μ ℓ x ≤ θ * ∑ i ∈ range (ℓ + 1), (m i : ℝ))
    (hfull : μ J x ≤ τ') :
    ∃ z : ℕ → Fin P → C → ℤ, (∀ i p c, z i p c ≠ 0 → i ≤ J ∧ g c ∈ Ks i) ∧
      (∀ i p c, (z i p c).natAbs ≤ m i) ∧
      x + ∑ i ∈ range (J + 1), ∑ p, wcls g (z i p) = 0 := by
  classical
  obtain ⟨u, hu, hux, hurec⟩ := chain_pay hS x hxG (by rw [hKc 0 (Nat.zero_le _)]; exact hx)
  rw [hbot, AddSubgroup.mem_bot] at hux
  have hcap := prefix_capacity A M P L J hJL m (fun ℓ => (wcost (u ℓ) : ℝ)) (fun ℓ => μ ℓ x)
    hθ0 hθ1 hτ hurec hloc hfull hP hm0 hSJ
  -- support of the step words
  have hus : ∀ ℓ c, u ℓ c ≠ 0 → ℓ ≤ J ∧ g c ∈ Ks ℓ := fun ℓ c h =>
    ⟨(hu ℓ c h).1, by rw [← hKc ℓ (hu ℓ c h).1]; exact (hu ℓ c h).2⟩
  -- the net word and its per-entry splitting
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
      -- `|w c| ≤ ∑_{ℓ ≤ t} cost (u ℓ) ≤ P S t`
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
        have h1 := hcap t htJ
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
  -- the total class equals the class of the net word
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

end S07V46
