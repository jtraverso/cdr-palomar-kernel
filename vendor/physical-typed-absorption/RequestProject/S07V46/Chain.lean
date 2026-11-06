/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-!
# V46 §2 — the finite-chain payment mechanism (abstract, exact)

Setting: an abelian group `Q` (later the actual `ClassQ`), a finite catalog `g : C → Q`, a
subgroup `G` containing every catalog charge (later: the classes of actual core profiles), a chain
of subgroups `Kc 0, Kc 1, …, Kc (J+1)` (later `K_{Z_0} ⊇ … ⊇ K_{Z_J} ⊇ ⊥`) and step monitors
`μ ℓ : Q → ℝ`.

`StepPay` is the one-step interface: at step `ℓ ≤ J`, every `y ∈ G ∩ Kc ℓ` is moved into `Kc (ℓ+1)`
by a word supported on entries with `g c ∈ Kc ℓ`, of cost `≤ A (1 + μ ℓ y)`, and `μ ℓ` grows by
at most `M` per unit of word cost.  (V44 `PhysicalMonitors.pay_prev` is exactly of this form.)

`chain_pay` : starting from `x ∈ G ∩ Kc 0`, words `u 0, …, u J` with
* `u ℓ` supported on `{c | g c ∈ Kc ℓ}`, zero for `ℓ > J`;
* `x + ∑_{ℓ ≤ J} [u ℓ] ∈ Kc (J+1)` EXACTLY (no approximation; torsion included);
* the recurrence `|u ℓ| ≤ A (1 + μ ℓ x + M ∑_{k<ℓ} |u k|)`, where the monitor is evaluated at the
  ORIGINAL charge `x` (the previous words are absorbed by the Lipschitz property).
-/

@[expose] public section

namespace S07V46

open Finset

variable {Q C : Type*} [AddCommGroup Q] [Fintype C]

/-- the class of a catalog word -/
def wcls (g : C → Q) (u : C → ℤ) : Q := ∑ c, u c • g c

/-- the cost (`ℓ¹` norm) of a catalog word -/
def wcost (u : C → ℤ) : ℕ := ∑ c, (u c).natAbs

lemma wcls_add (g : C → Q) (u v : C → ℤ) : wcls g (u + v) = wcls g u + wcls g v := by
  simp [wcls, add_smul, sum_add_distrib]

lemma wcls_sum (g : C → Q) {ι : Type*} (s : Finset ι) (u : ι → C → ℤ) :
    wcls g (fun c => ∑ i ∈ s, u i c) = ∑ i ∈ s, wcls g (u i) := by
  unfold wcls
  simp_rw [sum_smul]
  exact sum_comm

lemma wcost_sum_le {ι : Type*} (s : Finset ι) (u : ι → C → ℤ) :
    wcost (fun c => ∑ i ∈ s, u i c) ≤ ∑ i ∈ s, wcost (u i) := by
  unfold wcost
  rw [sum_comm]
  exact sum_le_sum fun c _ => Int.natAbs_sum_le _ _

lemma wcls_mem {g : C → Q} {G : AddSubgroup Q} (hg : ∀ c, g c ∈ G) (u : C → ℤ) :
    wcls g u ∈ G :=
  sum_mem fun c _ => zsmul_mem (hg c) _

/-- **one-step payment interface** along the chain `Kc` with step monitors `μ` -/
structure StepPay (g : C → Q) (G : AddSubgroup Q) (Kc : ℕ → AddSubgroup Q) (μ : ℕ → Q → ℝ)
    (A M J : ℕ) : Prop where
  /-- every catalog charge lies in `G` -/
  gen : ∀ c, g c ∈ G
  /-- payment of step `ℓ` -/
  pay : ∀ ℓ ≤ J, ∀ y ∈ G, y ∈ Kc ℓ → ∃ u : C → ℤ, (∀ c, u c ≠ 0 → g c ∈ Kc ℓ) ∧
    y + wcls g u ∈ Kc (ℓ + 1) ∧ (wcost u : ℝ) ≤ A * (1 + μ ℓ y)
  /-- Lipschitz growth of the step monitors under catalog words -/
  lip : ∀ ℓ ≤ J, ∀ y ∈ G, ∀ u : C → ℤ, μ ℓ (y + wcls g u) ≤ μ ℓ y + M * wcost u

/-- **Finite-chain payment (exact).** -/
theorem chain_pay {g : C → Q} {G : AddSubgroup Q} {Kc : ℕ → AddSubgroup Q} {μ : ℕ → Q → ℝ}
    {A M J : ℕ} (hS : StepPay g G Kc μ A M J) (x : Q) (hxG : x ∈ G) (hx : x ∈ Kc 0) :
    ∃ u : ℕ → C → ℤ, (∀ ℓ c, u ℓ c ≠ 0 → ℓ ≤ J ∧ g c ∈ Kc ℓ) ∧
      x + ∑ ℓ ∈ range (J + 1), wcls g (u ℓ) ∈ Kc (J + 1) ∧
      ∀ ℓ ≤ J, (wcost (u ℓ) : ℝ) ≤
        A * (1 + μ ℓ x + M * ∑ k ∈ range ℓ, (wcost (u k) : ℝ)) := by
  classical
  suffices key : ∀ t ≤ J + 1, ∃ u : ℕ → C → ℤ, (∀ ℓ c, u ℓ c ≠ 0 → ℓ < t ∧ g c ∈ Kc ℓ) ∧
      x + ∑ ℓ ∈ range t, wcls g (u ℓ) ∈ Kc t ∧
      ∀ ℓ < t, (wcost (u ℓ) : ℝ) ≤
        A * (1 + μ ℓ x + M * ∑ k ∈ range ℓ, (wcost (u k) : ℝ)) by
    obtain ⟨u, h1, h2, h3⟩ := key (J + 1) le_rfl
    exact ⟨u, fun ℓ c h => ⟨by have := (h1 ℓ c h).1; omega, (h1 ℓ c h).2⟩, h2,
      fun ℓ hℓ => h3 ℓ (by omega)⟩
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨fun _ _ => 0, fun _ _ h => absurd rfl h, by simpa using hx, fun _ h => absurd h (by omega)⟩
  | succ t ih =>
    intro ht
    obtain ⟨u, h1, h2, h3⟩ := ih (by omega)
    set y := x + ∑ ℓ ∈ range t, wcls g (u ℓ) with hy
    have hyG : y ∈ G := add_mem hxG (sum_mem fun ℓ _ => wcls_mem hS.gen _)
    obtain ⟨u', hu'1, hu'2, hu'3⟩ := hS.pay t (by omega) y hyG h2
    refine ⟨fun ℓ => if ℓ = t then u' else u ℓ, ?_, ?_, ?_⟩
    · intro ℓ c h
      by_cases hℓ : ℓ = t
      · subst hℓ; simp only [if_true] at h; exact ⟨by omega, hu'1 c h⟩
      · simp only [hℓ, if_false] at h
        exact ⟨by have := (h1 ℓ c h).1; omega, (h1 ℓ c h).2⟩
    · have hsum : ∑ ℓ ∈ range t, wcls g (if ℓ = t then u' else u ℓ) =
          ∑ ℓ ∈ range t, wcls g (u ℓ) :=
        sum_congr rfl fun ℓ hℓ => by rw [if_neg (by simp at hℓ; omega)]
      rw [sum_range_succ, hsum]
      dsimp only
      rw [if_pos rfl, ← add_assoc]
      exact hu'2
    · intro ℓ hℓ
      have hk : ∀ k ∈ range ℓ, (wcost (if k = t then u' else u k) : ℝ) = wcost (u k) := by
        intro k hk; simp at hk; rw [if_neg (by omega)]
      rw [sum_congr rfl hk]
      by_cases hlt : ℓ < t
      · dsimp only; rw [if_neg (by omega)]; exact h3 ℓ hlt
      · have hℓt : ℓ = t := by omega
        subst hℓt
        dsimp only
        rw [if_pos rfl]
        -- the monitor at `y` is controlled by the monitor at `x`
        have hflat : y = x + wcls g (fun c => ∑ k ∈ range ℓ, u k c) := by
          rw [hy, wcls_sum]
        have hlip := hS.lip ℓ (by omega) x hxG (fun c => ∑ k ∈ range ℓ, u k c)
        have hcost : (wcost (fun c => ∑ k ∈ range ℓ, u k c) : ℝ) ≤
            ∑ k ∈ range ℓ, (wcost (u k) : ℝ) := by
          exact_mod_cast wcost_sum_le (range ℓ) u
        have hmy : μ ℓ y ≤ μ ℓ x + M * ∑ k ∈ range ℓ, (wcost (u k) : ℝ) := by
          rw [hflat]
          calc μ ℓ (x + wcls g fun c => ∑ k ∈ range ℓ, u k c)
              ≤ μ ℓ x + M * wcost (fun c => ∑ k ∈ range ℓ, u k c) := hlip
            _ ≤ μ ℓ x + M * ∑ k ∈ range ℓ, (wcost (u k) : ℝ) := by
                gcongr
        calc (wcost u' : ℝ) ≤ A * (1 + μ ℓ y) := hu'3
          _ ≤ A * (1 + (μ ℓ x + M * ∑ k ∈ range ℓ, (wcost (u k) : ℝ))) := by
              gcongr
          _ = A * (1 + μ ℓ x + M * ∑ k ∈ range ℓ, (wcost (u k) : ℝ)) := by ring

end S07V46
