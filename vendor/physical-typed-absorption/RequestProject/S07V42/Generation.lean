/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.Atoms
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V42 §4 — compression data and bounded actual generators of every `K_Z`

**Compression data (named inputs, the shape exported by G1-Z compression).** The G1-Z
compression sources are not present in this tree; their outputs enter as the two structures
below, with all dimensions and constants fixed BEFORE the host:

* `CoreCompression H lab F W d c E` — ONE fixed coordinate map `q0` on the actual core module
  `M(H[W])` with `ker q0 ⊆ Λ_core`, `|q0 x i| ≤ c · l1E x`, `q0(Λ_core ∩ M(H[W])) = span S`,
  `S ⊆ [-E, E]^d`. Surjectivity is NOT required.
* `DelCompression H lab F Z d' c' E'` — the same shape for the deleted host `H − Z`, i.e. the
  module `M(H − Z)` and the lattice `Λ(H − Z)`.

Proved:

* `class_eq_iff`: for `x, y ∈ M(H[W])`, `[x] = [y]` in `Q` iff `q0 x ≡ q0 y` modulo `span S`
  (exact coordinate-class equality iff physical difference; from the kernel and image facts).
* `bounded_generators` (step 2): constants `genK` fixed from `(β, h, d, c, d', c', E')` before
  the host. For every admissible `Z` there is a finite set `Y` of ACTUAL vectors in
  `M(H[W \ Z]) ∩ Λ(H − Z)` with `l1E y ≤ genK`, such that every element of
  `M(H[W \ Z]) ∩ Λ(H − Z)` differs from an integer combination of `Y` by an element of
  `Λ_core ∩ Λ(H − Z)`. The proof feeds V37 `relative_kernel_generators` with the pair
  coordinate map `(q0, q_Z)` on `M(H[W \ Z])` (no compression of `H[W \ Z]` is needed) and with
  the bounded atoms of `bounded_atoms`.
* `KZ_eq_span`: `K_Z` is the span of the classes of these bounded vectors.
-/

open Finset Classical Submodule

noncomputable section

namespace S07V42

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal

variable {V I : Type*} [Fintype V]

/-- **Core compression data** (G1-Z export shape; a named input). -/
structure CoreCompression (H : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (W : Finset V) (d c E : ℕ) where
  /-- the coordinate map on the actual core module -/
  q : MCore H lab F W →ₗ[ℤ] (Fin d → ℤ)
  /-- kernel inside the intrinsic core lattice -/
  ker_le : ∀ x : MCore H lab F W, q x = 0 → (x : Sym2 V → ℤ) ∈ LamCore H lab F W
  /-- coordinate bound -/
  bound : ∀ (x : MCore H lab F W) (i : Fin d), |q x i| ≤ c * l1E (x : Sym2 V → ℤ)
  /-- generators of the image of the lattice -/
  S : Finset (Fin d → ℤ)
  /-- the generators are bounded -/
  S_bound : ∀ s ∈ S, ∀ i, |s i| ≤ E
  /-- the image identity -/
  img : ((LamCore H lab F W).comap (MCore H lab F W).subtype).map q =
    span ℤ (S : Set (Fin d → ℤ))

/-- **Deleted-host compression data** (G1-Z export shape for `H − Z`; a named input). -/
structure DelCompression (H : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (Z : Finset V) (d c E : ℕ) where
  /-- the coordinate map on `M(H − Z)` -/
  q : localProfile (S07V39.delG H Z) lab F →ₗ[ℤ] (Fin d → ℤ)
  /-- kernel inside `Λ(H − Z)` -/
  ker_le : ∀ x : localProfile (S07V39.delG H Z) lab F, q x = 0 →
    (x : Sym2 V → ℤ) ∈ LamDel H lab F Z
  /-- coordinate bound -/
  bound : ∀ (x : localProfile (S07V39.delG H Z) lab F) (i : Fin d),
    |q x i| ≤ c * l1E (x : Sym2 V → ℤ)
  /-- generators of the image of the lattice -/
  S : Finset (Fin d → ℤ)
  /-- the generators are bounded -/
  S_bound : ∀ s ∈ S, ∀ i, |s i| ≤ E
  /-- the image identity -/
  img : ((LamDel H lab F Z).comap (localProfile (S07V39.delG H Z) lab F).subtype).map q =
    span ℤ (S : Set (Fin d → ℤ))

variable {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V}

/-- membership in the image of the lattice -/
lemma CoreCompression.mem_span_iff {d c E : ℕ} (C : CoreCompression H lab F W d c E)
    (v : Fin d → ℤ) : v ∈ span ℤ (C.S : Set (Fin d → ℤ)) ↔
      ∃ l : MCore H lab F W, (l : Sym2 V → ℤ) ∈ LamCore H lab F W ∧ C.q l = v := by
  rw [← C.img]
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]

/-- **exact coordinate-class equality iff physical difference** -/
theorem CoreCompression.class_eq_iff {d c E : ℕ} (C : CoreCompression H lab F W d c E)
    (x y : MCore H lab F W) :
    clsQ H lab F W x = clsQ H lab F W y ↔ C.q x - C.q y ∈ span ℤ (C.S : Set (Fin d → ℤ)) := by
  unfold clsQ
  rw [Submodule.Quotient.eq, C.mem_span_iff]
  constructor
  · intro h
    exact ⟨x - y, by simpa using h, by simp⟩
  · rintro ⟨l, hl, hql⟩
    have hk : C.q (x - y - l) = 0 := by simp [hql]
    have := C.ker_le _ hk
    have h2 : (x : Sym2 V → ℤ) - (y : Sym2 V → ℤ) =
        ((x - y - l : MCore H lab F W) : Sym2 V → ℤ) + (l : Sym2 V → ℤ) := by
      simp only [Submodule.coe_sub]; abel
    rw [h2]
    exact add_mem this hl

/-- the pair coordinate map `(q0, q_Z)` on `M(H[W \ Z])` -/
def pairMap {d d' : ℕ} {M₀ M₁ M₂ : Submodule ℤ (Sym2 V → ℤ)} (h₁ : M₀ ≤ M₁) (h₂ : M₀ ≤ M₂)
    (A : M₁ →ₗ[ℤ] (Fin d → ℤ)) (B : M₂ →ₗ[ℤ] (Fin d' → ℤ)) : M₀ →ₗ[ℤ] (Fin (d + d') → ℤ) :=
  LinearMap.pi fun i => Fin.addCases (motive := fun _ => M₀ →ₗ[ℤ] ℤ)
    (fun j => (LinearMap.proj j).comp (A.comp (Submodule.inclusion h₁)))
    (fun j => (LinearMap.proj j).comp (B.comp (Submodule.inclusion h₂))) i

omit [Fintype V] in
lemma pairMap_left {d d' : ℕ} {M₀ M₁ M₂ : Submodule ℤ (Sym2 V → ℤ)} (h₁ : M₀ ≤ M₁)
    (h₂ : M₀ ≤ M₂) (A : M₁ →ₗ[ℤ] (Fin d → ℤ)) (B : M₂ →ₗ[ℤ] (Fin d' → ℤ)) (x : M₀)
    (j : Fin d) : pairMap h₁ h₂ A B x (Fin.castAdd d' j) = A (Submodule.inclusion h₁ x) j := by
  simp [pairMap]

omit [Fintype V] in
lemma pairMap_right {d d' : ℕ} {M₀ M₁ M₂ : Submodule ℤ (Sym2 V → ℤ)} (h₁ : M₀ ≤ M₁)
    (h₂ : M₀ ≤ M₂) (A : M₁ →ₗ[ℤ] (Fin d → ℤ)) (B : M₂ →ₗ[ℤ] (Fin d' → ℤ)) (x : M₀)
    (j : Fin d') : pairMap h₁ h₂ A B x (Fin.natAdd d j) = B (Submodule.inclusion h₂ x) j := by
  simp [pairMap]

/-- the uniform ℓ¹ bound of the generators of `K_Z`, fixed before the host -/
def genK (β : ℝ) (d c d' c' E' : ℕ) : ℕ :=
  S07V37.relK (d + d') d' (max c c') c' (atomR β) E'

/-- **Bounded actual generators of `K_Z` (step 2).** -/
theorem bounded_generators {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E)
    {Z : Finset V} (hZ : (Z.card : ℝ) ≤ coreDelta β h * W.card)
    (CZ : DelCompression H lab F Z d' c' E') :
    ∃ Y : Finset (Sym2 V → ℤ),
      (∀ y ∈ Y, y ∈ MZ H lab F W Z ∧ y ∈ LamDel H lab F Z ∧ l1E y ≤ genK β d c d' c' E') ∧
      ∀ x ∈ MZ H lab F W Z, x ∈ LamDel H lab F Z →
        ∃ f : (Sym2 V → ℤ) → ℤ, x - ∑ y ∈ Y, f y • y ∈ LamCore H lab F W ⊓ LamDel H lab F Z := by
  obtain ⟨hat, hspan⟩ := bounded_atoms H lab F W hβ hH3 hH4 hW hZ
  have h₁ := MZ_le_MCore H lab F W Z
  have h₂ := MZ_le_MDel H lab F W Z
  set qJ := pairMap h₁ h₂ C0.q CZ.q with hqJ
  have hkerJ : ∀ x : MZ H lab F W Z, qJ x = 0 →
      (x : Sym2 V → ℤ) ∈ LamCore H lab F W ⊓ LamDel H lab F Z := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have : C0.q (Submodule.inclusion h₁ x) = 0 := by
        funext j
        have := congrFun hx (Fin.castAdd d' j)
        rw [hqJ, pairMap_left] at this
        simpa using this
      exact C0.ker_le _ this
    · have : CZ.q (Submodule.inclusion h₂ x) = 0 := by
        funext j
        have := congrFun hx (Fin.natAdd d j)
        rw [hqJ, pairMap_right] at this
        simpa using this
      exact CZ.ker_le _ this
  have hqJb : ∀ (x : MZ H lab F W Z) i, |qJ x i| ≤ (max c c' : ℕ) * l1E (x : Sym2 V → ℤ) := by
    intro x i
    have hl : 0 ≤ l1E (x : Sym2 V → ℤ) := S07V37.l1E_L1Like.nonneg _
    induction i using Fin.addCases with
    | left j =>
      rw [hqJ, pairMap_left]
      refine (C0.bound _ j).trans (mul_le_mul_of_nonneg_right ?_ hl)
      exact_mod_cast le_max_left c c'
    | right j =>
      rw [hqJ, pairMap_right]
      refine (CZ.bound _ j).trans (mul_le_mul_of_nonneg_right ?_ hl)
      exact_mod_cast le_max_right c c'
  obtain ⟨Y, -, hY, hgen⟩ := S07V37.relative_kernel_generators (d + d') d' (max c c') c'
    (atomR β) E' l1E S07V37.l1E_L1Like (MZ H lab F W Z) (localProfile (S07V39.delG H Z) lab F)
    (LamCore H lab F W ⊓ LamDel H lab F Z) (LamDel H lab F Z) h₂ inf_le_right qJ CZ.q hkerJ
    CZ.ker_le hqJb CZ.bound CZ.S CZ.S_bound CZ.img (atomsZ H lab F W β Z) hat hspan
    (fun b hb => by exact_mod_cast hb.2)
  exact ⟨Y, hY, hgen⟩

/-- **`K_Z` is spanned by the classes of bounded actual vectors.** -/
theorem KZ_eq_span {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E)
    {Z : Finset V} (hZ : (Z.card : ℝ) ≤ coreDelta β h * W.card)
    (CZ : DelCompression H lab F Z d' c' E') :
    ∃ Y : Finset (Sym2 V → ℤ),
      (∀ y ∈ Y, y ∈ MZ H lab F W Z ∧ y ∈ LamDel H lab F Z ∧ l1E y ≤ genK β d c d' c' E') ∧
      KZ H lab F W Z = span ℤ (clsQ H lab F W '' (Y : Set (Sym2 V → ℤ))) := by
  obtain ⟨Y, hY, hgen⟩ := bounded_generators hβ hH3 hH4 hW C0 hZ CZ
  refine ⟨Y, hY, le_antisymm ?_ ?_⟩
  · intro k hk
    obtain ⟨x, hx1, hx2, rfl⟩ := (mem_KZ H lab F W).1 hk
    obtain ⟨f, hf⟩ := hgen x hx1 hx2
    have hcl : clsQ H lab F W x = ∑ y ∈ Y, f y • clsQ H lab F W y := by
      have : clsQ H lab F W (x - ∑ y ∈ Y, f y • y) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hf.1
      unfold clsQ at this ⊢
      rw [Submodule.Quotient.mk_sub, sub_eq_zero] at this
      rw [this, ← Submodule.mkQ_apply, map_sum]
      exact Finset.sum_congr rfl fun y _ => LinearMap.map_smul _ _ _
    rw [hcl]
    exact Submodule.sum_mem _ fun y hy =>
      Submodule.smul_mem _ _ (subset_span ⟨y, hy, rfl⟩)
  · rw [span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_KZ H lab F W).2 ⟨y, (hY y hy).1, (hY y hy).2.1, rfl⟩

end S07V42
