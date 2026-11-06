/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.QuotientBox
@[expose] public section

/-!
# V37 — uniform finite presentations of integer preimage modules

For a finite index type `ι`, columns `c : ι → ℤ^d` and a finite set `S ⊆ ℤ^d`, the
**actual integer preimage module** is

    presMod c S = { t : ι → ℤ | ∑ a, t a • c a ∈ span_ℤ S }.

No saturation is taken: membership is in `span_ℤ S` itself.

* `presentation_uniform` — given `ι`, `d`, `E`, there are constants `presK ι d E`
  (number of generators) and `presL ι d E` (ℓ¹ bound of the coefficient vectors) such that,
  for EVERY configuration with `c a ∈ [-E,E]^d` and `S ⊆ [-E,E]^d`, the module `presMod c S`
  is spanned by a finset `Z` with `#Z ≤ presK` and `∑ a, |z a| ≤ presL` for all `z ∈ Z`.

The proof is a maximum over the FINITE set of presentation configurations
`(ι → [-E,E]^d) × Finset [-E,E]^d`, of a chosen finite generating set of each preimage
module (`ℤ^ι` is Noetherian). It never takes a maximum over subgroups of a fixed-rank group.
-/

open Submodule Finset

noncomputable section
open Classical

namespace S07V37

open TypedTriangle.QuotientBox

variable {ι : Type*} [Fintype ι] {d : ℕ}

/-- The coefficient map `t ↦ ∑ a, t a • c a`. -/
def colMap (c : ι → Fin d → ℤ) : (ι → ℤ) →ₗ[ℤ] (Fin d → ℤ) where
  toFun t := ∑ a, t a • c a
  map_add' t s := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r t := by simp [Finset.smul_sum, mul_smul]

lemma colMap_apply (c : ι → Fin d → ℤ) (t : ι → ℤ) : colMap c t = ∑ a, t a • c a := rfl

/-- The actual integer preimage module `{t | ∑ a, t a • c a ∈ span_ℤ S}` (no saturation). -/
def presMod (c : ι → Fin d → ℤ) (S : Set (Fin d → ℤ)) : Submodule ℤ (ι → ℤ) :=
  (span ℤ S).comap (colMap c)

lemma mem_presMod {c : ι → Fin d → ℤ} {S : Set (Fin d → ℤ)} {t : ι → ℤ} :
    t ∈ presMod c S ↔ ∑ a, t a • c a ∈ span ℤ S := Iff.rfl

/-- ℓ¹ norm of a coefficient vector. -/
def l1c (z : ι → ℤ) : ℤ := ∑ a, |z a|

lemma l1c_nonneg (z : ι → ℤ) : 0 ≤ l1c z := Finset.sum_nonneg fun _ _ => abs_nonneg _

variable (ι d) in
/-- A presentation configuration: columns in the box and a subset of the box. -/
abbrev Cfg (E : ℕ) := (ι → {v // v ∈ box d E}) × Finset {v // v ∈ box d E}

/-- Columns of a configuration. -/
def Cfg.cols {E : ℕ} (κ : Cfg ι d E) : ι → Fin d → ℤ := fun a => (κ.1 a).1

/-- Image set of a configuration. -/
def Cfg.set {E : ℕ} (κ : Cfg ι d E) : Set (Fin d → ℤ) :=
  ((κ.2.map (Function.Embedding.subtype _) : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))

/-- A chosen finite generating set of the preimage module of a configuration. -/
def Cfg.gens {E : ℕ} (κ : Cfg ι d E) : Finset (ι → ℤ) :=
  Classical.choose (IsNoetherian.noetherian (presMod κ.cols κ.set))

lemma Cfg.span_gens {E : ℕ} (κ : Cfg ι d E) :
    span ℤ (κ.gens : Set (ι → ℤ)) = presMod κ.cols κ.set :=
  Classical.choose_spec (IsNoetherian.noetherian (presMod κ.cols κ.set))

variable (ι d) in
/-- Uniform bound on the number of chosen generators. -/
def presK (E : ℕ) : ℕ := (Finset.univ : Finset (Cfg ι d E)).sup fun κ => κ.gens.card

variable (ι d) in
/-- Uniform bound on the ℓ¹ norm of the chosen coefficient generators. -/
def presL (E : ℕ) : ℕ :=
  (Finset.univ : Finset (Cfg ι d E)).sup fun κ => κ.gens.sup fun z => (l1c z).toNat

/-- **Uniform finite presentation.** The constants `presK ι d E`, `presL ι d E` depend only
on `ι, d, E`. For every configuration of columns `c` and a finite set `S`, both inside the box
`[-E,E]^d`, the actual preimage module `presMod c S` is spanned by at most `presK` vectors,
each of ℓ¹ norm at most `presL`. -/
theorem presentation_uniform (E : ℕ) (c : ι → Fin d → ℤ) (hc : ∀ a i, |c a i| ≤ E)
    (S : Finset (Fin d → ℤ)) (hS : ∀ s ∈ S, ∀ i, |s i| ≤ E) :
    ∃ Z : Finset (ι → ℤ), Z.card ≤ presK ι d E ∧
      (∀ z ∈ Z, l1c z ≤ presL ι d E) ∧
      span ℤ (Z : Set (ι → ℤ)) = presMod c (S : Set (Fin d → ℤ)) := by
  let κ : Cfg ι d E := (fun a => ⟨c a, mem_box.2 (hc a)⟩, S.subtype (· ∈ box d E))
  have hcols : κ.cols = c := rfl
  have hset : κ.set = (S : Set (Fin d → ℤ)) := by
    simp only [Cfg.set, κ, Finset.subtype_map]
    congr 1
    exact Finset.filter_true_of_mem fun s hs => mem_box.2 (hS s hs)
  refine ⟨κ.gens, ?_, ?_, ?_⟩
  · exact Finset.le_sup (f := fun κ : Cfg ι d E => κ.gens.card) (Finset.mem_univ κ)
  · intro z hz
    have h1 : (l1c z).toNat ≤ κ.gens.sup fun z => (l1c z).toNat :=
      Finset.le_sup (f := fun z => (l1c z).toNat) hz
    have h2 : (κ.gens.sup fun z => (l1c z).toNat) ≤ presL ι d E :=
      Finset.le_sup (f := fun κ : Cfg ι d E => κ.gens.sup fun z => (l1c z).toNat)
        (Finset.mem_univ κ)
    have h3 := Int.self_le_toNat (l1c z)
    have : ((l1c z).toNat : ℤ) ≤ presL ι d E := by exact_mod_cast h1.trans h2
    linarith
  · rw [κ.span_gens, hcols, hset]

end S07V37
