/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Copies
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Topology

/-!
# Exact masses by convexity, in any dimension

`center_mem_convexHull`: if, for every vertex `v` of the cube `m₀ + [-R, R]^ι`, a point `p v`
lies within `E < R` (in every coordinate) of that vertex, then `m₀` is in the convex hull of the
points. Proof: separate `m₀` from the (compact) hull by a linear functional `f`
(Hahn–Banach); at the vertex opposite to the signs of the coefficients of `f`, every coordinate
term of `f (p v) - f m₀` is `≤ 0`. There is no loss in the dimension.

`seed_convex_sum`: finite convex combinations of diffuse seeds are diffuse seeds.

`exists_seed_exact_mass`: if seeds realise every vertex of the cube up to `E < R` in the linear
masses `μ ↦ Σ_Q μ Q · w i Q`, a convex combination realises `m₀` exactly.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle

/-- A linear functional on `ι → ℝ` in coordinates. -/
theorem clm_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) →L[ℝ] ℝ)
    (x : ι → ℝ) : f x = ∑ i, x i * f (Pi.single i 1) := by
  conv_lhs => rw [show x = ∑ i, x i • (Pi.single i 1 : ι → ℝ) by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  simp [map_smul, smul_eq_mul]

/-- **The centre of a perturbed cube lies in the convex hull of the perturbed vertices.** -/
theorem center_mem_convexHull {ι : Type*} [Fintype ι] [DecidableEq ι] (m₀ : ι → ℝ) {R E : ℝ}
    (hRE : E < R) (p : (ι → Bool) → (ι → ℝ))
    (hp : ∀ v i, |p v i - (m₀ i + (if v i then R else -R))| ≤ E) :
    m₀ ∈ convexHull ℝ (Set.range p) := by
  by_contra h
  have hfin : (Set.range p).Finite := Set.finite_range p
  obtain ⟨f, u, hfu, hb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    (Set.Finite.isClosed_convexHull (𝕜 := ℝ) hfin) h
  set c : ι → ℝ := fun i => f (Pi.single i 1) with hc
  let v : ι → Bool := fun i => decide (c i < 0)
  have hpv : p v ∈ convexHull ℝ (Set.range p) := subset_convexHull ℝ _ ⟨v, rfl⟩
  have h1 := hb (p v) hpv
  have hterm : ∀ i, c i * (p v i - m₀ i) ≤ 0 := by
    intro i
    have := hp v i
    rw [abs_le] at this
    by_cases hci : c i < 0
    · have hv : v i = true := by simp [v, hci]
      rw [hv, if_pos rfl] at this
      have : 0 ≤ p v i - m₀ i := by linarith
      nlinarith
    · have hv : v i = false := by simp [v, hci]
      rw [hv] at this
      simp only [Bool.false_eq_true, if_false] at this
      have : p v i - m₀ i ≤ 0 := by linarith
      push Not at hci
      nlinarith
  have h2 : f (p v) ≤ f m₀ := by
    rw [clm_apply_eq_sum f (p v), clm_apply_eq_sum f m₀]
    have : ∑ i, p v i * c i - ∑ i, m₀ i * c i ≤ 0 := by
      rw [← sum_sub_distrib]
      exact sum_nonpos fun i _ => by have := hterm i; nlinarith
    linarith
  linarith

/-- **Finite convex combinations of diffuse seeds.** -/
theorem seed_convex_sum {V I : Type*} [Fintype V] [DecidableEq V] {H : Host V I} {F : Set (Multiset I)} {C : ℝ}
    {κ : Type*} (s : Finset κ) (w : κ → ℝ) (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    (μ : κ → Finset V → ℝ) (hμ : ∀ i ∈ s, IsDiffuseSeed H F C (μ i)) :
    IsDiffuseSeed H F C (fun T => ∑ i ∈ s, w i * μ i T) := by
  refine ⟨fun T hT => ⟨?_, ?_⟩, fun e he => ?_⟩
  · calc 1 / (C * Fintype.card V) = ∑ i ∈ s, w i * (1 / (C * Fintype.card V)) := by
          rw [← sum_mul, hw1, one_mul]
      _ ≤ ∑ i ∈ s, w i * μ i T :=
          sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ((hμ i hi).1 T hT).1 (hw0 i hi)
  · calc ∑ i ∈ s, w i * μ i T ≤ ∑ i ∈ s, w i * (C / Fintype.card V) :=
          sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ((hμ i hi).1 T hT).2 (hw0 i hi)
      _ = C / Fintype.card V := by rw [← sum_mul, hw1, one_mul]
  · rw [sum_comm]
    simp_rw [← mul_sum]
    trans ∑ i ∈ s, w i * 1
    · exact sum_congr rfl fun i hi => by rw [(hμ i hi).2 e he]
    · simp [hw1]

/-- **Exact masses.** Seeds realising every vertex of the cube `m₀ + [-R, R]^ι` up to `E < R`
in the masses `μ ↦ Σ_{Q ∈ A} μ Q · w i Q` give a seed with masses exactly `m₀`. -/
theorem exists_seed_exact_mass {V I : Type*} [Fintype V] [DecidableEq V] {H : Host V I} {F : Set (Multiset I)}
    {C : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset (Finset V))
    (w : ι → Finset V → ℝ) (m₀ : ι → ℝ) {R E : ℝ} (hRE : E < R)
    (hv : ∀ v : ι → Bool, ∃ μ, IsDiffuseSeed H F C μ ∧
      ∀ i, |∑ Q ∈ A, μ Q * w i Q - (m₀ i + (if v i then R else -R))| ≤ E) :
    ∃ μ, IsDiffuseSeed H F C μ ∧ ∀ i, ∑ Q ∈ A, μ Q * w i Q = m₀ i := by
  classical
  choose μv hμv hmv using hv
  let p : (ι → Bool) → (ι → ℝ) := fun v i => ∑ Q ∈ A, μv v Q * w i Q
  have hmem := center_mem_convexHull m₀ hRE p (fun v i => hmv v i)
  have hrange : Set.range p = ((univ : Finset (ι → Bool)).image p : Set (ι → ℝ)) := by
    simp
  rw [hrange, Finset.mem_convexHull'] at hmem
  obtain ⟨wt, hw0, hw1, hsum⟩ := hmem
  -- weights on the vertices: put the weight of a point on one chosen preimage
  have hpre : ∀ y ∈ (univ : Finset (ι → Bool)).image p, ∃ v, p v = y := fun y hy => by
    obtain ⟨v, -, rfl⟩ := mem_image.1 hy; exact ⟨v, rfl⟩
  let S := (univ : Finset (ι → Bool)).image p
  let pick : (ι → ℝ) → (ι → Bool) := fun y =>
    if h : ∃ v, p v = y then Classical.choose h else fun _ => false
  have hpick : ∀ y ∈ S, p (pick y) = y := fun y hy => by
    simp only [pick, dif_pos (hpre y hy)]; exact Classical.choose_spec (hpre y hy)
  refine ⟨fun T => ∑ y ∈ S, wt y * μv (pick y) T,
    seed_convex_sum S wt hw0 hw1 (fun y => μv (pick y)) (fun y _ => hμv _), fun i => ?_⟩
  have h1 : ∑ Q ∈ A, (∑ y ∈ S, wt y * μv (pick y) Q) * w i Q =
      ∑ y ∈ S, wt y * p (pick y) i := by
    simp only [p, sum_mul, mul_assoc]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [mul_sum]
  rw [h1]
  have h2 : ∑ y ∈ S, wt y * p (pick y) i = ∑ y ∈ S, wt y * y i :=
    sum_congr rfl fun y hy => by rw [hpick y hy]
  rw [h2]
  have := congrFun hsum i
  simpa [Finset.sum_apply, smul_eq_mul] using this

end CDRBicolour.KBicolor
