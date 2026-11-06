/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07.Families
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace S07V24
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The path tail applies to a concrete available family fixed before the
sample, including paths whose internal vertices already avoid a prepared cut. -/
theorem fam_paths_for_available_family {a q : ℝ} {m : ℕ} (ha : 0 < a) (hq : 0 < q) (hq1 : q ≤ 1) (hm : 0 < m)
    (hn : 0 < Fintype.card V) (L : SimpleGraph V) [DecidableRel L.Adj] (x y : V)
    (I : Finset (L.Walk x y)) (hLength : ∀ p ∈ I, p.length = m+1)
    (hcount : a * (Fintype.card V : ℝ) ^ m ≤ I.card) :
    bprob q univ (fun W => ((I.filter (fun p => intlSet m p ⊆ W)).card : ℝ) <
        a * (Fintype.card V : ℝ) ^ m * q ^ m / 2) ≤
      Real.exp (-(a * q ^ (2 * m) / (16 * m ^ 2) * Fintype.card V)) := by
  set n := Fintype.card V
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hle : bprob q univ (fun W => ((I.filter (fun p => intlSet m p ⊆ W)).card : ℝ) <
        a * (n : ℝ) ^ m * q ^ m / 2) ≤
      bprob q univ (fun W => (ccount I (fun p => intlSet m p) W : ℝ) <
        a * (n : ℝ) ^ m * q ^ m / 2) :=
    bprob_mono hq.le hq1 (fun W h => by simpa [ccount, pathsIn] using h)
  refine hle.trans ((count_tail hq hq1 I (fun p => intlSet m p) hm
    (fun p _ => (card_image_le).trans (by simp)) (Δ := m * (n : ℝ) ^ (m - 1))
    (by positivity) ?_ hcount).trans ?_)
  · intro z
    have hA : ∀ p ∈ I, p.length = m + 1 := by
      exact hLength
    have := card_through_le m x y I hA {z}
    have heq : (I.filter fun p => z ∈ intlSet m p) =
        I.filter fun p => ∃ i : Fin m, intl m p i ∈ ({z} : Finset V) := by
      apply Finset.filter_congr; intro p _; simp [mem_intlSet]
    rw [heq]
    have h2 : ((I.filter fun p => ∃ i : Fin m, intl m p i ∈ ({z} : Finset V)).card : ℝ) ≤
        (({z} : Finset V).card * m * Fintype.card V ^ (m - 1) : ℕ) := by exact_mod_cast this
    push_cast at h2; simpa using h2
  · apply Real.exp_le_exp.2
    have e : a * (n : ℝ) ^ m * q ^ (2 * m) / (16 * (m * (n : ℝ) ^ (m - 1)) * m) =
        a * q ^ (2 * m) / (16 * m ^ 2) * n := by
      have : (n : ℝ) ^ m = (n : ℝ) ^ (m - 1) * n := by
        rw [← pow_succ, Nat.sub_add_cancel hm]
      rw [this]; field_simp
    rw [e]


#print axioms fam_paths_for_available_family
end S07V24
