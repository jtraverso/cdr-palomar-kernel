/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.RootedLoads
public import CDRBicolour.Absorption.Count.Wilson.Approx

/-!
# The actual approximate local seed with optimized scalar weights

The reference type weights come from the original SeedData. They are multiplied
by the LP-optimal weight for the number of reserve vertices. The edge-sum formula
splits exactly into group and reserve third-vertex kernel masses. It does not
assume a residual decomposition or that the local seed is already exact.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

/-- The existing type-weight edge-sum theorem also gives arbitrary triangle functions. -/
theorem sum_tri_edge_generic (lab : V → Fin k) {u v : V} (huv : u ≠ v)
    (μ : Finset V → ℝ) :
    (∑ T ∈ (triG lab (bicF k)).filter (fun T => s(u,v) ∈ triEdges T), μ T) =
      ∑ w ∈ univ.filter (fun w => w ≠ u ∧ w ≠ v ∧
        ({lab u, lab v, lab w} : Multiset (Fin k)) ∈ bicF k), μ {u,v,w} := by
  classical
  let FV : Set (Multiset V) := {m | m.map lab ∈ bicF k}
  have hA : allowed (⟨⊤, id⟩ : Host V V) FV = triG lab (bicF k) := by
    ext T
    simp [allowed, IsAllowed, triG, cHostG, FV]
  have hh := edge_sum_top (id : V → V) FV (fun m => μ m.toFinset) huv
  rw [hA] at hh
  simpa [FV] using hh

def approximateLocalSeed (lab : V → Fin k) (R : Finset V) (c : Fin k → ℕ)
    (a : Fin k → Fin k → ℝ) (g x y : ℝ) (T : Finset V) : ℝ :=
  optimalWeight g x y #(T.filter fun v => v ∈ R) * seedW c a (T.val.map lab)

theorem approximateLocalSeed_bounds (lab : V → Fin k) (R : Finset V)
    (c : Fin k → ℕ) (a : Fin k → Fin k → ℝ) {g x y η δ n : ℝ}
    (hg : 1 ≤ g) (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n) (hs : SeedData c η a)
    (hcls : ∀ i, δ * n ≤ c i) (hsize : ∀ i, (c i : ℝ) ≤ n) (h2 : 2 ≤ δ * n)
    {T : Finset V} (hT : T ∈ triG lab (bicF k)) :
    optimalFloor g x y * η / n ≤ approximateLocalSeed lab R c a g x y T ∧
      approximateLocalSeed lab R c a g x y T ≤ 2 / (δ * n * x) := by
  obtain ⟨hl, hu⟩ := seedW_sharp_bounds c a hη hδ hn hs hcls hsize h2 (gmem_tri.mp hT).2.2
  obtain ⟨hwl, hwu⟩ := optimalWeight_bounds hg hx hy hyx #(T.filter fun v => v ∈ R)
  have hfloor : 0 < optimalFloor g x y := by unfold optimalFloor; positivity
  have hweight := hfloor.le.trans hwl
  have hseed : 0 ≤ seedW c a (T.val.map lab) := (div_nonneg hη.le hn.le).trans hl
  constructor
  · have hmul := mul_le_mul hwl hl (div_nonneg hη.le hn.le) hweight
    simpa only [approximateLocalSeed, mul_div_assoc] using hmul
  · have hmul := mul_le_mul hwu hu hseed (by positivity : (0 : ℝ) ≤ 1 / x)
    calc
      _ ≤ (1 / x) * (2 / (δ * n)) := hmul
      _ = _ := by ring

/-- Exact splitting of each local edge load into the two third-vertex masses. -/
theorem approximateLocalSeed_edge_sum (lab : V → Fin k) (R : Finset V)
    (c : Fin k → ℕ) (a : Fin k → Fin k → ℝ) (g x y : ℝ) {u v : V} (huv : u ≠ v) :
    let j : ℕ := (if u ∈ R then 1 else 0) + (if v ∈ R then 1 else 0)
    let w : V → ℝ := fun z => classKernel c a (lab u) (lab v) (lab z)
    (∑ T ∈ (triG lab (bicF k)).filter (fun T => s(u,v) ∈ triEdges T),
      approximateLocalSeed lab R c a g x y T) =
      optimalWeight g x y j * ∑ z ∈ ((univ \ R).erase u).erase v, w z +
      optimalWeight g x y (j+1) * ∑ z ∈ (R.erase u).erase v, w z := by
  classical
  intro j w
  rw [sum_tri_edge_generic lab huv]
  let A := univ.filter fun z : V => z ≠ u ∧ z ≠ v
  let B := univ.filter fun z : V => z ≠ u ∧ z ≠ v ∧
    ({lab u, lab v, lab z} : Multiset (Fin k)) ∈ bicF k
  have hsum : (∑ z ∈ B, approximateLocalSeed lab R c a g x y {u,v,z}) =
      ∑ z ∈ A, optimalWeight g x y (j + if z ∈ R then 1 else 0) * w z := by
    have hB : B = A.filter fun z => ({lab u, lab v, lab z} : Multiset (Fin k)) ∈ bicF k := by
      ext z
      simp [A, B, and_assoc]
    rw [hB, sum_filter]
    apply sum_congr rfl
    intro z hz
    have hzu := (mem_filter.mp hz).2.1
    have hzv := (mem_filter.mp hz).2.2
    have hk := classKernel_eq c a (lab u) (lab v) (lab z)
    by_cases hf : ({lab u, lab v, lab z} : Multiset (Fin k)) ∈ bicF k
    · rw [if_pos hf]
      simp only [approximateLocalSeed]
      rw [CDRBicolour.Absorption.Count.Wilson.card_filter_triple _ huv hzu.symm hzv.symm,
        val_map_triple lab huv hzu hzv]
      rw [if_pos hf] at hk
      exact congrArg (fun q => optimalWeight g x y (j + if z ∈ R then 1 else 0) * q) hk
    · rw [if_neg hf]
      rw [if_neg hf] at hk
      change 0 = optimalWeight g x y (j + if z ∈ R then 1 else 0) *
        classKernel c a (lab u) (lab v) (lab z)
      rw [← hk, mul_zero]
  change (∑ z ∈ B, approximateLocalSeed lab R c a g x y {u,v,z}) = _
  rw [hsum, ← sum_filter_add_sum_filter_not A (fun z => z ∈ R)]
  have hRset : A.filter (fun z => z ∈ R) = (R.erase u).erase v := by
    ext z
    simp [A, and_comm, and_left_comm, and_assoc]
  have hGset : A.filter (fun z => z ∉ R) = ((univ \ R).erase u).erase v := by
    ext z
    simp [A, and_comm, and_left_comm, and_assoc]
  have hRsum : (∑ z ∈ A.filter (fun z => z ∈ R),
      optimalWeight g x y (j + if z ∈ R then 1 else 0) * w z) =
      optimalWeight g x y (j+1) * ∑ z ∈ (R.erase u).erase v, w z := by
    rw [mul_sum, ← hRset]
    exact sum_congr rfl fun z hz => by rw [if_pos (mem_filter.mp hz).2]
  have hGsum : (∑ z ∈ A.filter (fun z => z ∉ R),
      optimalWeight g x y (j + if z ∈ R then 1 else 0) * w z) =
      optimalWeight g x y j * ∑ z ∈ ((univ \ R).erase u).erase v, w z := by
    rw [mul_sum, ← hGset]
    exact sum_congr rfl fun z hz => by rw [if_neg (mem_filter.mp hz).2, Nat.add_zero]
  rw [hRsum, hGsum]
  ring

end CDRBicolour.KBicolor.Wilson
