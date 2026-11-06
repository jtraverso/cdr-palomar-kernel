/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V45.CoreProfile
@[expose] public section

/-!
# V45 §4 — the map to the TRUE core subtype

* `CoreSupp H W` — integer edge vectors supported on `edges(H[W])` (zero-extended);
* `origCoreProf_le_MCore` — under the contract, `localProfile H ⊓ CoreSupp H W ≤ MCore H lab F W`;
* `toMCore` — the corresponding ℤ-linear map (inclusion) into `MCore` (no new choice);
* `toCore` / `toCoreL` — restriction to the true core subtype `{a // a ∈ W}`, whose host is
  `H.comap Subtype.val` (the actual induced host `H[W]`, labels `lab ∘ Subtype.val`);
* `toCore_isLocalProfile` — the restriction is a local profile of the TRUE induced host, and its
  zero extension `liftE` is the original vector;
* `l1E_toCore` — exact `ℓ¹` identity; `toCore_apply` — exact coordinate identity.
-/

open Finset Classical

noncomputable section

namespace S07V45

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42

variable {V I : Type*} [Fintype V]

/-- integer edge vectors supported on the edges of `H[W]` -/
def CoreSupp (H : SimpleGraph V) (W : Finset V) : Submodule ℤ (Sym2 V → ℤ) where
  carrier := {x | ∀ e, e ∉ edges (indG H W) → x e = 0}
  add_mem' := fun hx hy e he => by simp [hx e he, hy e he]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r x hx e he => by simp [hx e he]

lemma mem_CoreSupp {H : SimpleGraph V} {W : Finset V} {x : Sym2 V → ℤ} :
    x ∈ CoreSupp H W ↔ ∀ e, e ∉ edges (indG H W) → x e = 0 := Iff.rfl

variable {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V} {t : ℕ}

/-- **the original core-supported profiles lie in `MCore`** -/
theorem origCoreProf_le_MCore (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t) :
    localProfile H lab F ⊓ CoreSupp H W ≤ MCore H lab F W :=
  fun _ hx => mem_MCore_of_contract hCt ht ht3 hx.1 hx.2

/-- the corresponding ℤ-linear map into `MCore` -/
def toMCore (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t) :
    ↥(localProfile H lab F ⊓ CoreSupp H W) →ₗ[ℤ] ↥(MCore H lab F W) :=
  Submodule.inclusion (origCoreProf_le_MCore hCt ht ht3)

lemma toMCore_val (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t)
    (x : ↥(localProfile H lab F ⊓ CoreSupp H W)) :
    ((toMCore hCt ht ht3 x : ↥(MCore H lab F W)) : Sym2 V → ℤ) = x := rfl

variable (W) in
/-- restriction of an ambient edge vector to the true core subtype -/
def toCore (x : Sym2 V → ℤ) : Sym2 {a // a ∈ W} → ℤ := x ∘ Sym2.map Subtype.val

variable (W) in
/-- the restriction as a ℤ-linear map -/
def toCoreL : (Sym2 V → ℤ) →ₗ[ℤ] (Sym2 {a // a ∈ W} → ℤ) :=
  LinearMap.funLeft ℤ ℤ (Sym2.map Subtype.val)

omit [Fintype V] in
lemma toCoreL_apply (x : Sym2 V → ℤ) : toCoreL W x = toCore W x := rfl

omit [Fintype V] in
lemma toCore_apply (x : Sym2 V → ℤ) (a b : {a // a ∈ W}) :
    toCore W x s(a, b) = x s(a.1, b.1) := rfl

/-- **the restriction is a local profile of the TRUE induced core host**, and its zero extension
is the original vector -/
theorem toCore_isLocalProfile (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t)
    {x : Sym2 V → ℤ} (hx : x ∈ localProfile H lab F) (hsupp : x ∈ CoreSupp H W) :
    IsLocalProfile (H.comap (Subtype.val : {a // a ∈ W} → V)) (lab ∘ Subtype.val) F
        (toCore W x) ∧
      liftE (ι := (Subtype.val : {a // a ∈ W} → V)) (toCore W x) = x := by
  have hM := mem_MCore_of_contract hCt ht ht3 hx hsupp
  have h := isLocalProfile_pull Subtype.val_injective (edgesIn_indG H W) hM
  rw [indG_comap] at h
  exact h

/-- membership in the local profile module of the true induced core host -/
theorem toCore_mem_localProfile (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t)
    {x : Sym2 V → ℤ} (hx : x ∈ localProfile H lab F) (hsupp : x ∈ CoreSupp H W) :
    toCore W x ∈ localProfile (H.comap (Subtype.val : {a // a ∈ W} → V))
      (lab ∘ Subtype.val) F :=
  (toCore_isLocalProfile hCt ht ht3 hx hsupp).1

/-- **exact `ℓ¹` identity** for core-supported vectors -/
theorem l1E_toCore {x : Sym2 V → ℤ} (hsupp : x ∈ CoreSupp H W) :
    l1E (toCore W x) = l1E x := by
  have hl : liftE (ι := (Subtype.val : {a // a ∈ W} → V)) (toCore W x) = x := by
    funext e
    by_cases h : ∃ e' : Sym2 {a // a ∈ W}, Sym2.map Subtype.val e' = e
    · obtain ⟨e', rfl⟩ := h
      exact liftE_map Subtype.val_injective _ e'
    · rw [liftE_of_not (ι := (Subtype.val : {a // a ∈ W} → V)) _ h]
      symm
      apply hsupp
      intro he
      rw [TypedTriangle.SparseEdge.mem_edges] at he
      induction e using Sym2.ind with
      | h a b =>
        rw [SimpleGraph.mem_edgeSet] at he
        exact h ⟨s(⟨a, he.2.1⟩, ⟨b, he.2.2⟩), by simp⟩
  have := l1E_liftE Subtype.val_injective (toCore W x)
  rw [hl] at this
  exact this.symm

end S07V45
