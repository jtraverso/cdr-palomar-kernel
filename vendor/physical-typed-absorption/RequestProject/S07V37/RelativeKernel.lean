/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V37.FinitePresentation
@[expose] public section

/-!
# V37 — bounded generators of the relative transport kernel (abstract form)

Ambient `ℤ`-module `N` with an ℓ¹-like size `ℓ` (nonnegative, subadditive,
`ℓ (z • x) ≤ |z| ℓ x`). Submodules `M₀ ≤ M₁` (local modules of `J ≤ G`) and `L₀ ≤ L₁`
(physical lattices). Inputs, all independently provable:

* coordinate maps `qJ : M₀ → ℤ^d`, `qG : M₁ → ℤ^{d'}` with `ker qJ ⊆ L₀`, `ker qG ⊆ L₁` and
  coordinate bounds `|q x i| ≤ c · ℓ x` (no surjectivity is assumed);
* the exact image identity `qG (L₁ ∩ M₁) = span_ℤ S` with `S ⊆ [-E,E]^{d'}` finite;
* a set of local atoms inside `M₀`, spanning `M₀`, each with `ℓ ≤ R`.

`relative_kernel_generators`: constants `k, K` depending ONLY on `d, d', cJ, cG, R, E` (chosen
before `N` and all data) such that there is a finset `Y` of ACTUAL elements `y ∈ M₀ ∩ L₁` with
`ℓ y ≤ k`, `#Y ≤ K`, and every `x ∈ M₀ ∩ L₁` differs, modulo `L₀`, from an integer combination
of `Y`. This is a statement about generation of `(M₀ ∩ L₁)/L₀` by classes (torsion retained);
`relative_kernel_quotient_span` states it on the quotient itself.

The proof follows the finite-presentation plan: one chosen atom per attained `qJ`-image in the
box `[-cJ R, cJ R]^d` (these generate `M₀` modulo `L₀` because `ker qJ ⊆ L₀`), the bounded
columns `qG(b_a)`, the actual preimage module `presMod` (membership ⇔ `∑ z_a b_a ∈ L₁` through
the image identity and `ker qG ⊆ L₁`, not saturation), and `presentation_uniform`.
-/

open Submodule Finset

noncomputable section
open Classical

namespace S07V37

open TypedTriangle.QuotientBox

/-- ℓ¹-like size on an additive group. -/
structure L1Like {N : Type*} [AddCommGroup N] (ℓ : N → ℤ) : Prop where
  nonneg : ∀ x, 0 ≤ ℓ x
  add_le : ∀ x y, ℓ (x + y) ≤ ℓ x + ℓ y
  smul_le : ∀ (z : ℤ) x, ℓ (z • x) ≤ |z| * ℓ x

lemma L1Like.zero {N : Type*} [AddCommGroup N] {ℓ : N → ℤ} (h : L1Like ℓ) : ℓ 0 = 0 := by
  have := h.smul_le 0 0
  simp only [zero_smul, abs_zero, zero_mul] at this
  exact le_antisymm this (h.nonneg 0)

lemma L1Like.sum_le {N : Type*} [AddCommGroup N] {ℓ : N → ℤ} (h : L1Like ℓ) {κ : Type*}
    (s : Finset κ) (z : κ → ℤ) (f : κ → N) :
    ℓ (∑ a ∈ s, z a • f a) ≤ ∑ a ∈ s, |z a| * ℓ (f a) := by
  induction s using Finset.induction_on with
  | empty => simp [h.zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h.add_le _ _).trans (add_le_add (h.smul_le _ _) ih)

/-- Uniform ℓ-bound for the kernel generators. -/
def relK (d d' cJ cG R E : ℕ) : ℕ :=
  presL {v // v ∈ box d (cJ * R)} d' (max (cG * R) E) * R

/-- Uniform bound on the number of kernel generators. -/
def relN (d d' cJ cG R E : ℕ) : ℕ :=
  presK {v // v ∈ box d (cJ * R)} d' (max (cG * R) E)

universe u

/-- **Bounded generators of the relative kernel (abstract finite-presentation theorem).** -/
theorem relative_kernel_generators (d d' cJ cG R E : ℕ)
    {N : Type u} [AddCommGroup N] (ℓ : N → ℤ) (hℓ : L1Like ℓ)
    (M₀ M₁ L₀ L₁ : Submodule ℤ N) (hM : M₀ ≤ M₁) (hL : L₀ ≤ L₁)
    (qJ : M₀ →ₗ[ℤ] (Fin d → ℤ)) (qG : M₁ →ₗ[ℤ] (Fin d' → ℤ))
    (hkerJ : ∀ x : M₀, qJ x = 0 → (x : N) ∈ L₀)
    (hkerG : ∀ x : M₁, qG x = 0 → (x : N) ∈ L₁)
    (hqJ : ∀ x : M₀, ∀ i, |qJ x i| ≤ cJ * ℓ x)
    (hqG : ∀ x : M₁, ∀ i, |qG x i| ≤ cG * ℓ x)
    (S : Finset (Fin d' → ℤ)) (hS : ∀ s ∈ S, ∀ i, |s i| ≤ E)
    (himg : (L₁.comap M₁.subtype).map qG = span ℤ (S : Set (Fin d' → ℤ)))
    (atoms : Set N) (hat : atoms ⊆ M₀) (hspan : M₀ ≤ span ℤ atoms)
    (hR : ∀ b ∈ atoms, ℓ b ≤ R) :
    ∃ Y : Finset N, Y.card ≤ relN d d' cJ cG R E ∧
      (∀ y ∈ Y, y ∈ M₀ ∧ y ∈ L₁ ∧ ℓ y ≤ relK d d' cJ cG R E) ∧
      ∀ x ∈ M₀, x ∈ L₁ → ∃ f : N → ℤ, x - ∑ y ∈ Y, f y • y ∈ L₀ := by
  set D := cJ * R with hD
  set E' := max (cG * R) E with hE'
  let ι := {v // v ∈ box d D}
  -- the box bound for atoms
  have hbox : ∀ b (hb : b ∈ atoms), qJ ⟨b, hat hb⟩ ∈ box d D := fun b hb =>
    mem_box.2 fun i => by
      have h1 := hqJ ⟨b, hat hb⟩ i
      have h2 : (cJ : ℤ) * ℓ b ≤ cJ * R := mul_le_mul_of_nonneg_left (hR b hb) (by positivity)
      push_cast [hD]; exact h1.trans h2
  -- chosen representatives
  let P : ι → Prop := fun a => ∃ b, ∃ hb : b ∈ atoms, qJ ⟨b, hat hb⟩ = a.1
  let rep : ι → N := fun a => if h : P a then h.choose else 0
  have rep_mem : ∀ a, rep a ∈ M₀ := by
    intro a; simp only [rep]; split_ifs with h
    · exact hat h.choose_spec.choose
    · exact zero_mem _
  have rep_ℓ : ∀ a, ℓ (rep a) ≤ R := by
    intro a; simp only [rep]; split_ifs with h
    · exact hR _ h.choose_spec.choose
    · rw [hℓ.zero]; positivity
  let repM : ι → M₀ := fun a => ⟨rep a, rep_mem a⟩
  have rep_spec : ∀ b (hb : b ∈ atoms), qJ (repM ⟨_, hbox b hb⟩) = qJ ⟨b, hat hb⟩ := by
    intro b hb
    have hP : P ⟨_, hbox b hb⟩ := ⟨b, hb, rfl⟩
    have : rep ⟨_, hbox b hb⟩ = hP.choose := dif_pos hP
    have e : repM ⟨_, hbox b hb⟩ = ⟨hP.choose, hat hP.choose_spec.choose⟩ := Subtype.ext this
    rw [e]; exact hP.choose_spec.choose_spec
  -- the combination map
  let comb : (ι → ℤ) →ₗ[ℤ] M₀ :=
    { toFun := fun t => ∑ a, t a • repM a
      map_add' := fun t s => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r t => by simp [Finset.smul_sum, mul_smul] }
  have comb_coe : ∀ t, ((comb t : M₀) : N) = ∑ a, t a • rep a := by
    intro t; show ((∑ a, t a • repM a : M₀) : N) = _
    rw [Submodule.coe_sum]; rfl
  -- Step 2: representatives generate `M₀` modulo `L₀`.
  have step2 : ∀ x ∈ span ℤ atoms, ∃ t : ι → ℤ, x - (comb t : N) ∈ L₀ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem b hb =>
      refine ⟨Pi.single ⟨_, hbox b hb⟩ 1, ?_⟩
      have hc : comb (Pi.single ⟨_, hbox b hb⟩ 1) = repM ⟨_, hbox b hb⟩ := by
        show ∑ a, (Pi.single (⟨_, hbox b hb⟩ : ι) (1 : ℤ) : ι → ℤ) a • repM a = _
        rw [Finset.sum_eq_single (⟨_, hbox b hb⟩ : ι)]
        · simp
        · intro a _ ha; simp [ha]
        · simp
      have h0 : qJ (⟨b, hat hb⟩ - repM ⟨_, hbox b hb⟩) = 0 := by
        rw [map_sub, rep_spec b hb, sub_self]
      have := hkerJ _ h0
      rw [hc]; simpa using this
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨t, ht⟩ := hx; obtain ⟨s, hs⟩ := hy
      refine ⟨t + s, ?_⟩
      have : x + y - (comb (t + s) : N) = (x - comb t) + (y - comb s) := by
        rw [map_add, Submodule.coe_add]; abel
      rw [this]; exact add_mem ht hs
    | smul r x _ hx =>
      obtain ⟨t, ht⟩ := hx
      refine ⟨r • t, ?_⟩
      have : r • x - (comb (r • t) : N) = r • (x - comb t) := by
        rw [map_smul, Submodule.coe_smul, smul_sub]
      rw [this]; exact smul_mem _ _ ht
  -- Step 3: columns and the membership criterion.
  let c : ι → Fin d' → ℤ := fun a => qG (Submodule.inclusion hM (repM a))
  have hc_box : ∀ a i, |c a i| ≤ E' := by
    intro a i
    have h1 := hqG (Submodule.inclusion hM (repM a)) i
    have h2 : (cG : ℤ) * ℓ (rep a) ≤ cG * R :=
      mul_le_mul_of_nonneg_left (rep_ℓ a) (by positivity)
    have h3 : ((cG * R : ℕ) : ℤ) ≤ E' := by exact_mod_cast le_max_left _ _
    push_cast at h3
    exact h1.trans (h2.trans h3)
  have hS' : ∀ s ∈ S, ∀ i, |s i| ≤ E' := fun s hs i =>
    (hS s hs i).trans (by exact_mod_cast le_max_right _ _)
  have hcol : ∀ t, colMap c t = qG (Submodule.inclusion hM (comb t)) := by
    intro t
    show ∑ a, t a • c a = qG (Submodule.inclusion hM (∑ a, t a • repM a))
    simp [map_sum, c]
  have crit : ∀ t, ((comb t : M₀) : N) ∈ L₁ ↔ t ∈ presMod c (S : Set (Fin d' → ℤ)) := by
    intro t
    rw [presMod, Submodule.mem_comap, hcol, ← himg]
    constructor
    · intro h; exact ⟨Submodule.inclusion hM (comb t), h, rfl⟩
    · rintro ⟨l, hl, hlq⟩
      have h0 : qG (Submodule.inclusion hM (comb t) - l) = 0 := by rw [map_sub, hlq, sub_self]
      have h1 := hkerG _ h0
      have h2 : (l : N) ∈ L₁ := hl
      have : ((comb t : M₀) : N) = ((Submodule.inclusion hM (comb t) - l : M₁) : N) + l := by
        simp
      rw [this]; exact add_mem h1 h2
  -- Step 4: uniform finite presentation.
  obtain ⟨Z, hZcard, hZl1, hZspan⟩ := presentation_uniform E' c hc_box S hS'
  -- Step 5: lift.
  let φ : (ι → ℤ) →ₗ[ℤ] N := M₀.subtype ∘ₗ comb
  have hφ : ∀ t, φ t = ∑ a, t a • rep a := comb_coe
  refine ⟨Z.image φ, Finset.card_image_le.trans hZcard, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    have hzP : z ∈ presMod c (S : Set (Fin d' → ℤ)) := hZspan ▸ subset_span hz
    refine ⟨(comb z).2, (crit z).2 hzP, ?_⟩
    rw [hφ]
    calc ℓ (∑ a, z a • rep a) ≤ ∑ a, |z a| * ℓ (rep a) := hℓ.sum_le _ _ _
      _ ≤ ∑ a, |z a| * R := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (rep_ℓ a) (abs_nonneg _)
      _ = l1c z * R := by rw [l1c, Finset.sum_mul]
      _ ≤ (presL ι d' E' : ℤ) * R :=
          mul_le_mul_of_nonneg_right (hZl1 z hz) (by positivity)
      _ = (relK d d' cJ cG R E : ℤ) := by rw [relK]; push_cast; rfl
  · intro x hx0 hx1
    obtain ⟨t, ht⟩ := step2 x (hspan hx0)
    have htL : ((comb t : M₀) : N) ∈ L₁ := by
      have : ((comb t : M₀) : N) = x - (x - comb t) := by abel
      rw [this]; exact sub_mem hx1 (hL ht)
    have htP : t ∈ span ℤ (Z : Set (ι → ℤ)) := hZspan ▸ (crit t).1 htL
    have hmem : φ t ∈ span ℤ ((Z.image φ : Finset N) : Set N) := by
      rw [Finset.coe_image, ← Submodule.map_span]
      exact Submodule.mem_map_of_mem htP
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hmem
    refine ⟨f, ?_⟩
    rw [hf]; exact ht

/-- The relative kernel `K = (M₀ ∩ L₁) / L₀` as a quotient of the submodule `M₀ ⊓ L₁`. -/
abbrev RelKer {N : Type*} [AddCommGroup N] (M₀ L₀ L₁ : Submodule ℤ N) :=
  ↥(M₀ ⊓ L₁) ⧸ L₀.comap (M₀ ⊓ L₁).subtype

/-- **Quotient form.** If a finset `Y ⊆ M₀ ∩ L₁` has the generation property of
`relative_kernel_generators`, then the classes of the elements of `Y` span the relative kernel
`(M₀ ∩ L₁)/L₀` as a `ℤ`-module (torsion included). -/
theorem relative_kernel_quotient_span {N : Type*} [AddCommGroup N]
    (M₀ L₀ L₁ : Submodule ℤ N) (Y : Finset N) (hY : ∀ y ∈ Y, y ∈ M₀ ∧ y ∈ L₁)
    (hgen : ∀ x ∈ M₀, x ∈ L₁ → ∃ f : N → ℤ, x - ∑ y ∈ Y, f y • y ∈ L₀) :
    span ℤ (Set.range fun y : Y =>
      (Submodule.Quotient.mk ⟨y.1, (hY y.1 y.2).1, (hY y.1 y.2).2⟩ : RelKer M₀ L₀ L₁)) = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨f, hf⟩ := hgen x.1 x.2.1 x.2.2
    let g : Y → (M₀ ⊓ L₁ : Submodule ℤ N) := fun y => ⟨y.1, (hY y.1 y.2).1, (hY y.1 y.2).2⟩
    have hx : Submodule.Quotient.mk x =
        (Submodule.Quotient.mk (∑ y : Y, f y.1 • g y) : RelKer M₀ L₀ L₁) := by
      rw [Submodule.Quotient.eq]
      show ((x - ∑ y : Y, f y.1 • g y : (M₀ ⊓ L₁ : Submodule ℤ N)) : N) ∈ L₀
      rw [Submodule.coe_sub, Submodule.coe_sum]
      simp only [Submodule.coe_smul, g]
      rw [Finset.sum_coe_sort Y (fun y => f y • y)]
      exact hf
    rw [hx, ← Submodule.mkQ_apply, map_sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    rw [map_smul, Submodule.mkQ_apply]
    exact Submodule.smul_mem _ _ (subset_span ⟨y, rfl⟩)

end S07V37
