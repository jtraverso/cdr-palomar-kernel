/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.Cross

/-!
# Placing bounded Latin patterns in the prescribed colour classes

The only capacity requirement is `g * m_i * t ≤ c_i` in each colour. We construct
the embedding fibre by fibre, preserving the prescribed labels. Thus a finite
Latin pattern, including `Pattern.exists_kbls`, supplies a Wilson `Setup` whenever
its replicated slots fit in the host. `proportional_fit` checks this requirement
from approximation of proportions and a small reserved fraction of the points.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Finset

/-- Fibrewise capacity suffices for a label-preserving embedding. -/
theorem exists_labelled_embedding {U V C : Type*} [Fintype U] [Fintype V]
    [Fintype C] [DecidableEq C] (f : U → C) (lab : V → C)
    (hfit : ∀ X, Fintype.card {u // f u = X} ≤ Fintype.card {v // lab v = X}) :
    ∃ e : U ↪ V, ∀ u, lab (e u) = f u := by
  classical
  have hf : ∀ X, Nonempty ({u // f u = X} ↪ {v // lab v = X}) :=
    fun X => Function.Embedding.nonempty_of_card_le (hfit X)
  let E := fun X => Classical.choice (hf X)
  let e : U ↪ V := (Equiv.sigmaFiberEquiv f).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl C) E).trans
      (Equiv.sigmaFiberEquiv lab).toEmbedding)
  refine ⟨e, fun u => ?_⟩
  change lab (E (f u) ⟨u, rfl⟩).val = f u
  exact (E (f u) ⟨u, rfl⟩).property

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}

theorem card_slot_fibre (κ : A → Fin k) (X : Fin k) :
    Fintype.card {u : Fin g × A × Fin t // κ u.2.1 = X} =
      g * Hilton.csize κ X * t := by
  let e : {u : Fin g × A × Fin t // κ u.2.1 = X} ≃
      Fin g × {a // κ a = X} × Fin t :=
    { toFun := fun u => (u.val.1, ⟨u.val.2.1, u.property⟩, u.val.2.2)
      invFun := fun u => ⟨(u.1, u.2.1.val, u.2.2), u.2.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_fin, Hilton.csize]
  ring

/-- Any bicoloured Latin pattern can be placed whenever the replicated slots fit. -/
theorem exists_setup (lab : Fin n → Fin k) (κ : A → Fin k) (τ : A → A → A)
    (hrow : ∀ P, Function.Bijective (τ P))
    (hcol : ∀ Q, Function.Bijective (fun P => τ P Q))
    (hbic : ∀ P Q, Pattern.bic (κ P) (κ Q) (κ (τ P Q)))
    (hfit : ∀ X, g * Hilton.csize κ X * t ≤ ksz lab X) :
    Nonempty (Setup lab κ g t) := by
  classical
  obtain ⟨e, he⟩ := exists_labelled_embedding
    (fun u : Fin g × A × Fin t => κ u.2.1) lab (fun X => by
      rw [card_slot_fibre]
      simpa only [ksz, Fintype.card_subtype] using hfit X)
  refine ⟨⟨e, (fun i P α => he (i, P, α)), τ,
    (fun P => (hrow P).1), (fun Q => (hcol Q).1),
    (fun P => (hrow P).2), (fun Q => (hcol Q).2), fun P Q => ?_⟩⟩
  apply mem_bicF.mpr
  rcases hbic P Q with ⟨h, hne⟩ | ⟨hne, h | h⟩
  · exact Or.inl ⟨h, by simpa only [h] using hne.symm⟩
  · exact Or.inr (Or.inl ⟨h.symm, hne⟩)
  · exact Or.inr (Or.inr ⟨h.symm, hne⟩)

/-- Reserving a fraction `ρ` absorbs an error at most `ρ δ` in each proportion. -/
theorem proportional_fit {N m c n g t : ℕ} {δ ε ρ : ℝ}
    (hN : 0 < N) (hn : 0 < n) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ ρ * δ) (hc : δ * n ≤ c)
    (hclose : (m : ℝ) / N ≤ (c : ℝ) / n + ε)
    (hsize : ((g * t * N : ℕ) : ℝ) ≤ (1 - ρ) * n) :
    g * m * t ≤ c := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : (g : ℝ) * t * N ≤ (1 - ρ) * n := by exact_mod_cast hsize
  have heps : ε * n ≤ ρ * c := by nlinarith
  have hmn : 0 ≤ (m : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNR.le
  have hcn : 0 ≤ (c : ℝ) / n + ε := by positivity
  have hbound : (1 - ρ) * n * ((c : ℝ) / n + ε) ≤ c := by
    have hcancel : (n : ℝ) * ((c : ℝ) / n + ε) = c + ε * n := by
      field_simp
    rw [mul_assoc, hcancel]
    nlinarith [mul_nonneg hρ (mul_nonneg hε (Nat.cast_nonneg n))]
  have hmul : (g : ℝ) * m * t ≤ c := calc
    (g : ℝ) * m * t = ((g : ℝ) * t * N) * ((m : ℝ) / N) := by field_simp
    _ ≤ ((1 - ρ) * n) * ((c : ℝ) / n + ε) :=
      mul_le_mul hscale hclose hmn (by positivity)
    _ ≤ c := hbound
  exact_mod_cast hmul

end CDRBicolour.KBicolor.Wilson
