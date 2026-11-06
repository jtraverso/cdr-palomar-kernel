/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V28.PlacementGreedy
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# Quantitative simultaneous placement (V28)

Constants fixed BEFORE the host and the family, from the piece-size bound `k`, the absorber
size bound `s` and the robustness ratio `β` of the single-piece supply only:

* `plM β = ⌈1/β⌉₊ + 1`, saturation cap `plQ s β r = 2 s · plM β · r + 1` (proportional to
  `r + 1`, independent of the number of pieces);
* `plK s β = s (1 + 2 s · plM β) + 1`, `plEps k s β = β / (2 (1 + k + s + 2 s² plM β))`,
  `plN0 s β = ⌈2 s / β⌉₊ + 1`.

`simultaneous_absorbers`: for every host of order `n ≥ plN0`, every finite family of pieces
with supports `≤ k`, local incidence `≤ r`, every `B` with `Δ(B) ≤ b`, `r, b ≤ plEps · n`, if
every nonempty piece has the robust supply with size `s` and avoidance budgets `⌊β n⌋₊`, then
the absorbers exist simultaneously with global degree `≤ plK · (r + 1)`.
-/

open Finset

noncomputable section
open Classical

namespace S07V28

open TypedTriangle.SparseEdge

/-- `⌈1/β⌉₊ + 1`. -/
def plM (β : ℝ) : ℕ := ⌈1 / β⌉₊ + 1

/-- Saturation cap. -/
def plQ (s : ℕ) (β : ℝ) (r : ℕ) : ℕ := 2 * s * plM β * r + 1

/-- Degree constant. -/
def plK (s : ℕ) (β : ℝ) : ℕ := s * (1 + 2 * s * plM β) + 1

/-- Incidence/forbidden-degree ratio. -/
def plEps (k s : ℕ) (β : ℝ) : ℝ := β / (2 * (1 + k + s + 2 * s * s * plM β))

/-- Threshold on the order of the host. -/
def plN0 (s : ℕ) (β : ℝ) : ℕ := ⌈2 * s / β⌉₊ + 1

lemma plEps_pos (k s : ℕ) {β : ℝ} (hβ : 0 < β) : 0 < plEps k s β := by
  unfold plEps; positivity

lemma plQ_deg_le (s r : ℕ) (β : ℝ) : s * (r + plQ s β r) ≤ plK s β * (r + 1) := by
  unfold plQ plK
  have : (s * (1 + 2 * s * plM β) + 1) * (r + 1) =
      s * (r + (2 * s * plM β * r + 1)) + 2 * s * s * plM β + (r + 1) := by ring
  omega

lemma plQ_le (s r : ℕ) (β : ℝ) : plQ s β r ≤ plK s β * (r + 1) := by
  unfold plQ plK
  have h1 : s ≤ s * s := Nat.le_mul_self s
  have h2 : 2 * s * plM β * r ≤ 2 * (s * s) * plM β * r := by
    have := Nat.mul_le_mul_right (plM β * r) (Nat.mul_le_mul_left 2 h1)
    calc 2 * s * plM β * r = 2 * s * (plM β * r) := by ring
      _ ≤ 2 * (s * s) * (plM β * r) := this
      _ = 2 * (s * s) * plM β * r := by ring
  have : (s * (1 + 2 * s * plM β) + 1) * (r + 1) =
      2 * (s * s) * plM β * r + 1 + (s * (r + 1) + 2 * (s * s) * plM β + r) := by ring
  omega

/-- The forbidden-degree budget. -/
lemma plWindow_D (k s r b n : ℕ) {β : ℝ} (hβ : 0 < β) (hn : plN0 s β ≤ n)
    (hr : (r : ℝ) ≤ plEps k s β * n) (hb : (b : ℝ) ≤ plEps k s β * n) :
    b + k * r + s * (r + plQ s β r) ≤ ⌊β * n⌋₊ := by
  apply Nat.le_floor
  set m := plM β
  set C : ℝ := 1 + k + s + 2 * s * s * m with hC
  have hCpos : 0 < C := by positivity
  have hε : plEps k s β * C = β / 2 := by
    unfold plEps; rw [← hC]; field_simp
  have hs : (s : ℝ) ≤ β * n / 2 := by
    have h1 : (2 * s / β : ℝ) ≤ n := by
      have := Nat.le_ceil (2 * s / β : ℝ)
      have h2 : ((⌈2 * s / β⌉₊ : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (Nat.le_succ _).trans hn
      linarith
    rw [div_le_iff₀ hβ] at h1
    linarith
  have hkey : (b : ℝ) + r * (k + s + 2 * s * s * m) ≤ plEps k s β * n * C := by
    have h1 : (r : ℝ) * (k + s + 2 * s * s * m) ≤ plEps k s β * n * (k + s + 2 * s * s * m) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    rw [hC]; nlinarith
  have hcast : ((b + k * r + s * (r + plQ s β r) : ℕ) : ℝ) =
      (b : ℝ) + r * (k + s + 2 * s * s * m) + s := by
    unfold plQ; push_cast; ring
  rw [hcast]
  have : plEps k s β * n * C = β * n / 2 := by
    rw [mul_right_comm, hε]; ring
  linarith

/-- The saturation budget. -/
lemma plWindow_sigma (s r n : ℕ) {β : ℝ} (hβ : 0 < β) :
    2 * s * (n * r) < plQ s β r * (⌊β * n⌋₊ + 1) := by
  set m := plM β
  set σ := ⌊β * n⌋₊
  have hn : n ≤ m * (σ + 1) := by
    have h1 : β * n < (σ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : (1 / β : ℝ) ≤ m := by
      have := Nat.le_ceil (1 / β)
      simp only [m, plM]; push_cast; linarith
    have h3 : (n : ℝ) ≤ m * (σ + 1) := by
      have h4 : (n : ℝ) = (1 / β) * (β * n) := by field_simp
      rw [h4]
      have h5 : 0 ≤ (1 / β : ℝ) := by positivity
      calc (1 / β) * (β * n) ≤ (1 / β) * ((σ : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left h1.le h5
        _ ≤ m * (σ + 1) := mul_le_mul_of_nonneg_right h2 (by positivity)
    exact_mod_cast h3
  have : 2 * s * (n * r) ≤ 2 * s * m * r * (σ + 1) := by
    have := Nat.mul_le_mul_left (2 * s * r) hn
    calc 2 * s * (n * r) = 2 * s * r * n := by ring
      _ ≤ 2 * s * r * (m * (σ + 1)) := this
      _ = 2 * s * m * r * (σ + 1) := by ring
  unfold plQ
  calc 2 * s * (n * r) ≤ 2 * s * m * r * (σ + 1) := this
    _ < 2 * s * m * r * (σ + 1) + (σ + 1) := by omega
    _ = (2 * s * m * r + 1) * (σ + 1) := by ring

universe u v w

/-- **Simultaneous terminal absorbers for a catalogue of pieces (conditional on the robust
single-piece supply).** Constants depend only on `k`, `s`, `β`; global degree is controlled by
the local incidence `r`, not by the number of pieces. -/
theorem simultaneous_absorbers (k s : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K n₀ : ℕ, ∃ q : ℕ → ℕ, (∀ r, q r ≤ K * (r + 1)) ∧
    ∀ {V : Type u} [Fintype V] {I : Type v} {ι : Type w} [Fintype ι]
      (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
      (P : ι → Finset (Sym2 V)) (B : Finset (Sym2 V)) (r b : ℕ),
      n₀ ≤ Fintype.card V →
      (r : ℝ) ≤ ε * Fintype.card V → (b : ℝ) ≤ ε * Fintype.card V →
      (∀ i, (support (P i)).card ≤ k) → (∀ v, rootInc P v ≤ r) → (∀ v, degIn B v ≤ b) →
      (∀ i, P i ≠ ∅ → RobustAbsorberSupply G lab F (P i) s
        ⌊β * Fintype.card V⌋₊ ⌊β * Fintype.card V⌋₊) →
      ∃ A : ι → Finset (Sym2 V),
        (∀ i, P i = ∅ → A i = ∅) ∧
        (∀ i, IsAbsorber G lab F (P i) (A i)) ∧
        (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
        (∀ i, Disjoint (A i) B) ∧
        (∀ i j, Disjoint (A i) (P j)) ∧
        (∀ i, (A i).card ≤ s) ∧
        (∀ v, auxCount P A v ≤ q r) ∧
        (∀ v, degIn (univ.biUnion A) v ≤ K * (r + 1)) := by
  refine ⟨plEps k s β, plEps_pos k s hβ, plK s β, plN0 s β, plQ s β, fun r => ?_, ?_⟩
  · exact plQ_le s r β
  · intro V _ I ι _ G lab F P B r b hn hr hb hk hinc hB hsup
    obtain ⟨A, h1, h2, h3, h4, h5, h6, h7, h8⟩ := greedy_placement G lab F P B k r b s
      ⌊β * Fintype.card V⌋₊ ⌊β * Fintype.card V⌋₊ (plQ s β r) hk hinc hB hsup
      (plWindow_D k s r b _ hβ hn hr hb) (plWindow_sigma s r _ hβ)
    exact ⟨A, h1, h2, h3, h4, h5, h6, h7, fun v => (h8 v).trans (plQ_deg_le s r β)⟩

end S07V28
