/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V37.RelativeKernel
public import RequestProject.S07V37.NativeDeletion
public import RequestProject.TypedTriangle.LocalProfileModule
@[expose] public section

/-!
# V37 — the native relative transport kernel of two hosts `J ≤ G`

Two hosts `J ≤ G` on the same vertex set, with the same labels `lab` and the same allowed
types `F`. Actual objects (no saturation, no abstract model):

* `M_J = localProfile J lab F`, `M_G = localProfile G lab F` (V16 local profile modules);
* `Λ_J = lattice J lab F`, `Λ_G = lattice G lab F` (original integer lattices);
* the ambient edge module `Sym2 V → ℤ` with `l1E`.

Proved here:

* `localProfile_mono`, `lattice_mono` — `M_J ≤ M_G`, `Λ_J ≤ Λ_G`.
* `l1E_L1Like` — `l1E` is ℓ¹-like.
* `routing_atoms_H3H4` — from the ORIGINAL H3/H4 of `J` alone and `n ≥ n₀(α,h)`, the local
  atoms `{b ∈ M_J | l1E b ≤ 3 routeD α}` span `M_J` (routing cells of `routing_budget_real`, with
  `hlow` and `hdel` derived in `NativeDeletion`; the zero profile is handled separately).
* `native_relative_kernel` — **native endpoint.** Constants `k, K` are fixed from
  `(α, d, d', cJ, cG, E)` BEFORE the host. For every pair `J ≤ G` such that `J` satisfies H3/H4
  with `(α, h)` and `n ≥ routeN0 α h`, `n ≥ n1Of α`, and for coordinate maps
  `q_J : M_J → ℤ^d`, `q_G : M_G → ℤ^{d'}` with kernels inside `Λ_J`, `Λ_G`, coordinate bounds
  `|q x i| ≤ c · l1E x`, and the exact image identity `q_G(Λ_G ∩ M_G) = span S`,
  `S ⊆ [-E,E]^{d'}`, there is a finset `Y` of actual integer profiles `y ∈ M_J ∩ Λ_G` with
  `l1E y ≤ k`, `#Y ≤ K`, such that every `x ∈ M_J ∩ Λ_G` differs modulo `Λ_J` from an integer
  combination of `Y`; equivalently the classes of `Y` span `(M_J ∩ Λ_G)/Λ_J` (torsion kept).

The compression maps `q_J`, `q_G` are inputs of the shape exported by G1-Z compression
(`QuotientBox`/`PhysicalGrouping` consume the same shape); they are not constructed here.
-/

open Finset Classical Submodule

noncomputable section

namespace S07V37

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.ActiveCover
open TypedTriangle.Composition TypedTriangle.Dispersal TypedTriangle.RoutingConstants
open TypedTriangle.RoutingInputs TypedTriangle.ComponentCount
open S07V25 (n1Of)

variable {V I : Type*} [Fintype V]

omit [Fintype V] in
lemma isAllowed_mono {J G : SimpleGraph V} (hJG : J ≤ G) {lab : V → I} {F : Set (Multiset I)}
    {T : Finset V} (hT : IsAllowed J lab F T) : IsAllowed G lab F T :=
  ⟨hT.1, fun x hx y hy hxy => hJG (hT.2.1 x hx y hy hxy), hT.2.2⟩

omit [Fintype V] in
/-- `Λ_J ≤ Λ_G` (original lattices). -/
theorem lattice_mono {J G : SimpleGraph V} (hJG : J ≤ G) (lab : V → I) (F : Set (Multiset I)) :
    lattice J lab F ≤ lattice G lab F :=
  span_mono (Set.image_mono fun _ hT => isAllowed_mono hJG hT)

/-- `M_J ≤ M_G` (local profile modules). -/
theorem localProfile_mono {J G : SimpleGraph V} (hJG : J ≤ G) (lab : V → I)
    (F : Set (Multiset I)) : localProfile J lab F ≤ localProfile G lab F := by
  rintro x ⟨hx1, hx2⟩
  refine ⟨fun e he => hx1 e fun he' => he ?_, fun v => ?_⟩
  · simp only [edges, mem_filter, mem_univ, true_and] at he' ⊢
    exact (SimpleGraph.edgeSet_mono hJG) he'
  · obtain ⟨c, hc⟩ := hx2 v
    refine ⟨fun T => if IsAllowed J lab F T then c T else 0, fun w hw => ?_⟩
    rw [hc w hw, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext T
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hT, hv⟩, hw⟩; exact ⟨⟨⟨isAllowed_mono hJG hT, hv⟩, hw⟩, hT⟩
    · rintro ⟨⟨⟨-, hv⟩, hw⟩, hT⟩; exact ⟨⟨hT, hv⟩, hw⟩

/-- `l1E` is ℓ¹-like. -/
theorem l1E_L1Like : L1Like (l1E : (Sym2 V → ℤ) → ℤ) where
  nonneg x := Finset.sum_nonneg fun _ _ => abs_nonneg _
  add_le x y := by
    unfold l1E
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun e _ => abs_add_le _ _
  smul_le z x := by
    unfold l1E
    rw [Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl fun e _ => by simp [abs_mul])

/-- the routing deletion rate used for the atoms -/
def atomδ (α : ℝ) (h : ℕ) : ℝ := min (routeδ α h) (delOf α h)

/-- the local atoms of `M_J`: local profiles of `l1E ≤ 3 routeD α` -/
def atoms (J : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (α : ℝ) :
    Set (Sym2 V → ℤ) :=
  {b | IsLocalProfile J lab F b ∧ l1E b ≤ 3 * routeD α}

/-- **Bounded local atoms generate `M_J`**, from the ORIGINAL H3/H4 of `J`. -/
theorem routing_atoms_H3H4 {α : ℝ} {h : ℕ} (hα : 0 < α) {J : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} (hH3 : CommonNbrCond J lab F α) (hH4 : HingeCond J lab F α h)
    (hn₀ : routeN0 α h ≤ Fintype.card V) (hn₁ : n1Of α ≤ Fintype.card V) :
    atoms J lab F α ⊆ localProfile J lab F ∧
      localProfile J lab F ≤ span ℤ (atoms J lab F α) := by
  refine ⟨fun b hb => hb.1, ?_⟩
  intro x hx
  have hxE : EdgeSupp J x := hx.1
  by_cases h0 : norm1 J x = 0
  · rw [eq_zero_of_norm1_eq_zero hxE h0]; exact zero_mem _
  have he : 0 < norm1 J x := lt_of_le_of_ne (norm1_nonneg x) (Ne.symm h0)
  obtain ⟨hn, hrows, hdeg, -⟩ := routing_inputs_host hα h J lab F (hlow_of_H3 hH3) hn₀
  have hδ : 0 < atomδ α h := lt_min (routeδ_pos hα h) (delOf_pos hα h)
  have hδC : (compConst α : ℝ) * atomδ α h ≤ 4 :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans
      (compConst_mul_routeδ_le α h)
  have hdel : ∀ A : Finset V, (A.card : ℝ) ≤ atomδ α h * Fintype.card V →
      DeletionHyp J lab F A := fun A hA =>
    deletionHyp_H3H4 hα hH3 hH4 hn₁ A (hA.trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (by positivity)))
  obtain ⟨cells, hc1, hc2, -, hc4, -, -⟩ := routing_budget_real x hx (atomδ α h) hδ hδC he hn
    hrows hdeg hdel (one_le_routeD α) (routeD_spec α)
  have hsum : x = cells.sum := by
    funext e; rw [← hc2 e, Pi.list_sum_apply]
  rw [hsum]
  refine list_sum_mem fun b hb => subset_span ⟨hc1 b hb, ?_⟩
  rw [l1E_eq_norm1 (hc1 b hb).1]; exact hc4 b hb

/-- the uniform ℓ¹ bound of the native kernel generators -/
def nativeK (α : ℝ) (d d' cJ cG E : ℕ) : ℕ := relK d d' cJ cG (3 * routeD α) E

/-- the uniform bound on the number of native kernel generators -/
def nativeN (α : ℝ) (d d' cJ cG E : ℕ) : ℕ := relN d d' cJ cG (3 * routeD α) E

/-- **Native endpoint: bounded physical generators of the relative transport kernel.**
`nativeK α d d' cJ cG E` and `nativeN α d d' cJ cG E` are fixed before the host. -/
theorem native_relative_kernel {α : ℝ} {h : ℕ} (hα : 0 < α) (d d' cJ cG E : ℕ)
    {J G : SimpleGraph V} (hJG : J ≤ G) {lab : V → I} {F : Set (Multiset I)}
    (hH3 : CommonNbrCond J lab F α) (hH4 : HingeCond J lab F α h)
    (hn₀ : routeN0 α h ≤ Fintype.card V) (hn₁ : n1Of α ≤ Fintype.card V)
    (qJ : localProfile J lab F →ₗ[ℤ] (Fin d → ℤ)) (qG : localProfile G lab F →ₗ[ℤ] (Fin d' → ℤ))
    (hkerJ : ∀ x : localProfile J lab F, qJ x = 0 → (x : Sym2 V → ℤ) ∈ lattice J lab F)
    (hkerG : ∀ x : localProfile G lab F, qG x = 0 → (x : Sym2 V → ℤ) ∈ lattice G lab F)
    (hqJ : ∀ x : localProfile J lab F, ∀ i, |qJ x i| ≤ cJ * l1E (x : Sym2 V → ℤ))
    (hqG : ∀ x : localProfile G lab F, ∀ i, |qG x i| ≤ cG * l1E (x : Sym2 V → ℤ))
    (S : Finset (Fin d' → ℤ)) (hS : ∀ s ∈ S, ∀ i, |s i| ≤ E)
    (himg : ((lattice G lab F).comap (localProfile G lab F).subtype).map qG =
      span ℤ (S : Set (Fin d' → ℤ))) :
    ∃ Y : Finset (Sym2 V → ℤ), Y.card ≤ nativeN α d d' cJ cG E ∧
      (∀ y ∈ Y, y ∈ localProfile J lab F ∧ y ∈ lattice G lab F ∧
        l1E y ≤ nativeK α d d' cJ cG E) ∧
      ∀ x ∈ localProfile J lab F, x ∈ lattice G lab F →
        ∃ f : (Sym2 V → ℤ) → ℤ, x - ∑ y ∈ Y, f y • y ∈ lattice J lab F := by
  obtain ⟨hat, hspan⟩ := routing_atoms_H3H4 hα hH3 hH4 hn₀ hn₁
  exact relative_kernel_generators d d' cJ cG (3 * routeD α) E l1E l1E_L1Like
    (localProfile J lab F) (localProfile G lab F) (lattice J lab F) (lattice G lab F)
    (localProfile_mono hJG lab F) (lattice_mono hJG lab F) qJ qG hkerJ hkerG hqJ hqG S hS himg
    (atoms J lab F α) hat hspan (fun b hb => by exact_mod_cast hb.2)

/-- **Native endpoint, quotient form.** Same hypotheses; the classes of the bounded actual
profiles `Y ⊆ M_J ∩ Λ_G` span the relative kernel `(M_J ∩ Λ_G)/Λ_J` (torsion retained). -/
theorem native_relative_kernel_span {α : ℝ} {h : ℕ} (hα : 0 < α) (d d' cJ cG E : ℕ)
    {J G : SimpleGraph V} (hJG : J ≤ G) {lab : V → I} {F : Set (Multiset I)}
    (hH3 : CommonNbrCond J lab F α) (hH4 : HingeCond J lab F α h)
    (hn₀ : routeN0 α h ≤ Fintype.card V) (hn₁ : n1Of α ≤ Fintype.card V)
    (qJ : localProfile J lab F →ₗ[ℤ] (Fin d → ℤ)) (qG : localProfile G lab F →ₗ[ℤ] (Fin d' → ℤ))
    (hkerJ : ∀ x : localProfile J lab F, qJ x = 0 → (x : Sym2 V → ℤ) ∈ lattice J lab F)
    (hkerG : ∀ x : localProfile G lab F, qG x = 0 → (x : Sym2 V → ℤ) ∈ lattice G lab F)
    (hqJ : ∀ x : localProfile J lab F, ∀ i, |qJ x i| ≤ cJ * l1E (x : Sym2 V → ℤ))
    (hqG : ∀ x : localProfile G lab F, ∀ i, |qG x i| ≤ cG * l1E (x : Sym2 V → ℤ))
    (S : Finset (Fin d' → ℤ)) (hS : ∀ s ∈ S, ∀ i, |s i| ≤ E)
    (himg : ((lattice G lab F).comap (localProfile G lab F).subtype).map qG =
      span ℤ (S : Set (Fin d' → ℤ))) :
    ∃ Y : Finset (Sym2 V → ℤ), ∃ hY : ∀ y ∈ Y, y ∈ localProfile J lab F ∧ y ∈ lattice G lab F,
      Y.card ≤ nativeN α d d' cJ cG E ∧ (∀ y ∈ Y, l1E y ≤ nativeK α d d' cJ cG E) ∧
      span ℤ (Set.range fun y : Y => (Submodule.Quotient.mk ⟨y.1, (hY y.1 y.2).1, (hY y.1 y.2).2⟩ :
        RelKer (localProfile J lab F) (lattice J lab F) (lattice G lab F))) = ⊤ := by
  obtain ⟨Y, hcard, hY, hgen⟩ := native_relative_kernel hα d d' cJ cG E hJG hH3 hH4 hn₀ hn₁
    qJ qG hkerJ hkerG hqJ hqG S hS himg
  have hY' : ∀ y ∈ Y, y ∈ localProfile J lab F ∧ y ∈ lattice G lab F :=
    fun y hy => ⟨(hY y hy).1, (hY y hy).2.1⟩
  exact ⟨Y, hY', hcard, fun y hy => (hY y hy).2.2,
    relative_kernel_quotient_span _ _ _ Y hY' hgen⟩

end S07V37
