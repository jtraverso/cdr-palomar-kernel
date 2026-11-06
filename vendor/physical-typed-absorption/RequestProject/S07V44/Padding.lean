/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V34.Box
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V44 §1 — V34 monitors with a UNIFORM number of coordinates `kmax`

V34 `uniform_monitor_payment_indexB` gives, for each bounded presentation `(S, D) ⊆ B`, a monitor
`ψ : Qt S ⧸ Hgrp S D →+ ℤ^k` whose dimension `k` depends on `(S, D)`.  Since `B` is finite there are
finitely many presentations, so `kmax = max k` is fixed by `(d, B)` alone.  Zero-padding
`padL : ℤ^k →+ ℤ^K` (`k ≤ K`) preserves `ℓ¹` exactly (`l1_padL`) and is injective (`padL_injective`),
hence preserves the finite kernel, the generator bound `M` and the payment bound.

* `uniform_monitor_payment_kmax d B`: `∃ A M K`, fixed from `(d, B)`, such that every `(S, D) ⊆ B`
  has a monitor into `ℤ^K` with finite kernel, `‖ψ b‖₁ ≤ M` on `B`, and the indexed payment.
-/

open Finset

namespace S07V44

open S07V32 S07V34

/-- zero padding `ℤ^k → ℤ^K` -/
def padL (k K : ℕ) : (Fin k → ℤ) →+ (Fin K → ℤ) where
  toFun f i := if h : (i : ℕ) < k then f ⟨i, h⟩ else 0
  map_zero' := by funext i; simp
  map_add' f g := by
    funext i
    by_cases h : (i : ℕ) < k <;> simp [h]

lemma padL_apply_castLE {k K : ℕ} (hk : k ≤ K) (f : Fin k → ℤ) (j : Fin k) :
    padL k K f (Fin.castLE hk j) = f j := by
  simp [padL, j.2]

lemma padL_injective {k K : ℕ} (hk : k ≤ K) : Function.Injective (padL k K) := by
  intro f g h
  funext j
  have := congrFun h (Fin.castLE hk j)
  rwa [padL_apply_castLE, padL_apply_castLE] at this

/-- **zero padding preserves `ℓ¹` exactly** -/
lemma l1_padL {k K : ℕ} (hk : k ≤ K) (f : Fin k → ℤ) : l1 (padL k K f) = l1 f := by
  unfold l1
  let e : Fin k ↪ Fin K := Fin.castLEEmb hk
  have hsub : (univ.map e) ⊆ (univ : Finset (Fin K)) := subset_univ _
  rw [← sum_subset hsub, sum_map]
  · exact sum_congr rfl fun j _ => by
      simp only [e, Fin.castLEEmb_apply]
      rw [padL_apply_castLE]
  · intro i _ hi
    have hik : ¬ (i : ℕ) < k := by
      intro h
      exact hi (mem_map.2 ⟨⟨i, h⟩, mem_univ _, by ext; simp [e]⟩)
    simp [padL, hik]

/-- **V34 indexed uniform payment with a uniform target dimension `K`.** -/
theorem uniform_monitor_payment_kmax (d : ℕ) (B : Finset (Fin d → ℤ)) :
    ∃ A M K : ℕ, ∀ S D : Finset (Fin d → ℤ), S ⊆ B → D ⊆ B →
      ∃ psi : Qt S ⧸ Hgrp S D →+ (Fin K → ℤ),
        (psi.ker : Set (Qt S ⧸ Hgrp S D)).Finite ∧
        (∀ b ∈ B, l1 (psi ((qmk S b : Qt S) : Qt S ⧸ Hgrp S D)) ≤ M) ∧
        ∀ C : Finset (Fin d → ℤ), C ⊆ B → ∀ x ∈ Kgrp S C, ∃ z : (Fin d → ℤ) → ℤ,
          (∀ b, b ∉ C → z b = 0) ∧
          x + ∑ b ∈ B, z b • qmk S b ∈ Hgrp S D ∧
            ∑ b ∈ B, |z b| ≤ (A : ℤ) * (1 + l1 (psi (x : Qt S ⧸ Hgrp S D))) := by
  classical
  obtain ⟨A, M, h⟩ := uniform_monitor_payment_indexB d B
  choose k psi hker hM hpay using h
  let kf : Finset (Fin d → ℤ) × Finset (Fin d → ℤ) → ℕ := fun t =>
    if ht : t.1 ⊆ B ∧ t.2 ⊆ B then k t.1 t.2 ht.1 ht.2 else 0
  obtain ⟨K, hK⟩ := exists_bound_finset (B.powerset ×ˢ B.powerset) kf
  refine ⟨A, M, K, fun S D hS hD => ?_⟩
  have hkK : k S D hS hD ≤ K := by
    have := hK (S, D) (mem_product.2 ⟨mem_powerset.2 hS, mem_powerset.2 hD⟩)
    simpa [kf, hS, hD] using this
  refine ⟨(padL _ K).comp (psi S D hS hD), ?_, ?_, ?_⟩
  · refine (hker S D hS hD).subset ?_
    intro x hx
    have hx' : padL (k S D hS hD) K (psi S D hS hD x) = padL (k S D hS hD) K 0 := by
      rw [map_zero]; exact hx
    exact padL_injective hkK hx'
  · intro b hb
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [l1_padL hkK]
    exact hM S D hS hD b hb
  · intro C hC x hx
    obtain ⟨z, hz0, hz, hb⟩ := hpay S D hS hD C hC x hx
    refine ⟨z, hz0, hz, ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [l1_padL hkK]
    exact hb

end S07V44
