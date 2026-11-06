/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10.TriangleInstance
public import RequestProject.TypedTriangle.SparseEdgeDefs

@[expose] public section

/-!
# V22 / S10: adapter to the physical lattice of the existing sparse definitions

The existing (unchanged) file `TypedTriangle/SparseEdgeDefs.lean` defines the permitted
triangles `IsAllowed G lab F` and the physical lattice
`lattice G lab F = span_ℤ {ind (triEdges T) | T permitted}`. Here:

* `allowedTri G lab F`: the finite set of permitted triangles;
* `mem_lattice_iff_intImage`: the physical lattice is EXACTLY the integer image of
  `triMat (allowedTri G lab F)` (no saturation);
* `intCertProvider_of_lattice`: a provider stated on the physical lattice is an
  `IntCertProvider` of the triangle matrix;
* `realCert_physical`: realification on the physical host;
* `smooth_inverse_physical`: the CONDITIONAL S10 (1.2) on the physical host, with the
  local kernel (3.1) as explicit input.
-/

open Finset

noncomputable section

namespace S10V22

open TypedTriangle.SparseEdge

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- The finite set of permitted triangles of `(G, lab, F)`. -/
def allowedTri (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) : Finset (Finset V) :=
  by classical exact univ.filter (fun T => IsAllowed G lab F T)

omit [DecidableEq V] in
lemma mem_allowedTri {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {T : Finset V} : T ∈ allowedTri G lab F ↔ IsAllowed G lab F T := by
  classical
  unfold allowedTri
  simp

omit [Fintype V] in
lemma triEdges_eq_edgesOf (T : Finset V) : triEdges T = edgesOf T := by
  ext e
  simp [triEdges, edgesOf]

lemma triMat_col_of_allowed {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {T : Finset V} (hT : IsAllowed G lab F T) :
    (fun e => triMat (allowedTri G lab F) e T) = ind (triEdges T) := by
  funext e
  have hT' : T ∈ allowedTri G lab F := mem_allowedTri.2 hT
  simp only [triMat, ind, triEdges_eq_edgesOf, hT', true_and]

lemma triMat_col_of_not_allowed {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {T : Finset V} (hT : ¬ IsAllowed G lab F T) :
    (fun e => triMat (allowedTri G lab F) e T) = 0 := by
  funext e
  have hT' : T ∉ allowedTri G lab F := fun h => hT (mem_allowedTri.1 h)
  simp [triMat, hT']

/-- **The physical lattice is exactly the integer image of the triangle matrix.** -/
theorem mem_lattice_iff_intImage (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (y : Sym2 V → ℤ) : y ∈ lattice G lab F ↔ y ∈ intImage (triMat (allowedTri G lab F)) := by
  set A := triMat (allowedTri G lab F) with hA
  have hint : ∀ z, intOp A z = ∑ T, z T • (fun e => A e T) := by
    intro z; funext e; simp [intOp, Finset.sum_apply, mul_comm]
  constructor
  · intro hy
    unfold lattice at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨T, hT, rfl⟩ := hy
      refine ⟨Pi.single T 1, ?_⟩
      rw [hint]
      simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        mem_univ, if_true]
      rw [hA, triMat_col_of_allowed hT]
    | zero => exact ⟨0, by funext e; simp [intOp]⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨z₁, rfl⟩ := h₁
      obtain ⟨z₂, rfl⟩ := h₂
      exact ⟨z₁ + z₂, by funext e; simp [intOp, mul_add, Finset.sum_add_distrib]⟩
    | smul c y _ h =>
      obtain ⟨z, rfl⟩ := h
      exact ⟨c • z, by funext e; simp [intOp, Finset.mul_sum, mul_left_comm]⟩
  · rintro ⟨z, rfl⟩
    rw [hint]
    refine Submodule.sum_mem _ fun T _ => Submodule.smul_mem _ _ ?_
    by_cases hT : IsAllowed G lab F T
    · rw [hA, triMat_col_of_allowed hT]
      exact Submodule.subset_span ⟨T, hT, rfl⟩
    · rw [hA, triMat_col_of_not_allowed hT]
      exact Submodule.zero_mem _

/-- A congestion provider stated on the physical lattice `Λ_H` (form (1.1)/P05-CERT) is an
`IntCertProvider` of the triangle matrix. -/
theorem intCertProvider_of_lattice {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {K n : ℝ}
    (h : ∀ y ∈ lattice G lab F, ∃ z : Finset V → ℤ,
      intOp (triMat (allowedTri G lab F)) z = y ∧ l1 (castV z) ≤ K * l1 (castV y) ∧
      ∀ v, load (triTw (allowedTri G lab F)) v (castV z) ≤
        K * (inLoad edgeEw v (castV y) + l1 (castV y) / n + 1)) :
    IntCertProvider (triMat (allowedTri G lab F)) (triTw (allowedTri G lab F)) edgeEw K n :=
  fun y hy => h y ((mem_lattice_iff_intImage G lab F y).2 hy)

/-- **Realification on the physical host (CONDITIONAL on the provider).** -/
theorem realCert_physical {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {K n : ℝ}
    (hprov : IntCertProvider (triMat (allowedTri G lab F)) (triTw (allowedTri G lab F))
      edgeEw K n)
    {x : Sym2 V → ℝ} (hx : x ∈ realImage (triMat (allowedTri G lab F))) :
    RealCert (triMat (allowedTri G lab F)) (triTw (allowedTri G lab F)) edgeEw K n x :=
  realCert_of_realImage hprov hx

/-- Integer physical vectors lie in the real physical image. -/
theorem castV_mem_realImage_of_lattice {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {y : Sym2 V → ℤ} (hy : y ∈ lattice G lab F) :
    castV y ∈ realImage (triMat (allowedTri G lab F)) :=
  castV_mem_realImage _ ((mem_lattice_iff_intImage G lab F y).1 hy)

/-- **S10 (1.2) on the physical host, CONDITIONAL** on the provider (1.1), the degree
condition `d_e ≥ n/C` (permitted thirds), `n ≥ 2C`, and the local kernel (3.1). -/
theorem smooth_inverse_physical {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {C K L Dc : ℝ} (hC : 0 < C) (hn : 2 * C ≤ (Fintype.card V : ℝ))
    (hdeg : DegreeCond (allowedTri G lab F) C) (hK : 0 ≤ K) (hL : 0 ≤ L) (hDc : 0 ≤ Dc)
    (hprov : IntCertProvider (triMat (allowedTri G lab F)) (triTw (allowedTri G lab F))
      edgeEw K (Fintype.card V : ℝ))
    (Ker : LocalKernel (realOp (triMat (allowedTri G lab F))) (allowedTri G lab F) L Dc)
    {x : Sym2 V → ℝ} (hx : x ∈ realImage (triMat (allowedTri G lab F))) {xmax : ℝ}
    (hxmax : ∀ e, |x e| ≤ xmax) :
    ∃ w : Finset V → ℝ, realOp (triMat (allowedTri G lab F)) w = x ∧
      ∀ S, |w S| ≤ (6 * C + 3 * K / 2 * (L * (3 * Dc ^ 2 + Dc ^ 3 / 3) + 36 * C ^ 2)) *
        xmax / (Fintype.card V : ℝ) :=
  smooth_inverse_of_kernel (fun _ hT => (mem_allowedTri.1 hT).1) hC hn hdeg hK hL hDc hprov
    Ker hx hxmax

end S10V22
