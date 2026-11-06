/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Robustez: cota `L` de cambios estrictos en una cadena de sobreyecciones (P04, (L8)–(L10))

Parte algebraica del paso §4 del ledger. Para una sobreyección `f : B ↠ A` de grupos
abelianos finitamente generados (vistos como `ℤ`-módulos):

* `finrank_eq_add_finrank_ker`: `rank B = rank A + rank (ker f)`;
* `ker_le_torsion_of_finrank_eq`: si los rangos coinciden, `ker f` es de torsión;
* `torsion_card_of_surjective`: si `ker f` es de torsión, `|Tor B| = |ker f| · |Tor A|`;
* `strict_step`: si `f` no es inyectiva, o bien el rango aumenta, o bien el rango se
  conserva y el orden de la torsión se multiplica por al menos dos.

Y la parte combinatoria:

* `strict_count_le`: en una cadena de invariantes `(r_k, t_k)` con `r_k ≤ d`, `1 ≤ t_k ≤ T`,
  en la que cada paso estricto aumenta el rango o, a rango constante, duplica la torsión
  (y los pasos no estrictos conservan ambos invariantes), el número de pasos estrictos es a
  lo sumo `L = d + (d + 1) ⌊log₂ T⌋`, exactamente la constante (L8).

La sobreyección (L9) `Q_{J−Z} → Q_J` para los grupos físicos concretos (que requiere la
geometría de enlaces de P01 y la eliminación de S16) y la uniformidad de las cotas de rango y
torsión (de G1-Z, P02) NO están formalizadas aquí.
-/

open Module

noncomputable section

namespace TypedTriangle.Robust

universe u

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

/-- Nulidad-rango para sobreyecciones de `ℤ`-módulos finitamente generados. -/
theorem finrank_eq_add_finrank_ker (f : B →ₗ[ℤ] A) (hf : Function.Surjective f)
    [Module.Finite ℤ B] :
    finrank ℤ B = finrank ℤ A + finrank ℤ (LinearMap.ker f) := by
  have := LinearMap.rank_eq_of_surjective hf
  have hA : Module.Finite ℤ A := Module.Finite.of_surjective f hf
  rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at this
  exact_mod_cast this

/-- A rango constante, el núcleo de una sobreyección es de torsión. -/
theorem ker_le_torsion_of_finrank_eq (f : B →ₗ[ℤ] A) (hf : Function.Surjective f)
    [Module.Finite ℤ B] (h : finrank ℤ A = finrank ℤ B) :
    LinearMap.ker f ≤ Submodule.torsion ℤ B := by
  have h1 := finrank_eq_add_finrank_ker f hf
  have h0 : finrank ℤ (LinearMap.ker f) = 0 := by omega
  have hr : Module.rank ℤ (LinearMap.ker f) = 0 := by
    rw [← finrank_eq_rank, h0]; simp
  rw [rank_eq_zero_iff] at hr
  intro x hx
  obtain ⟨a, ha, hax⟩ := hr ⟨x, hx⟩
  rw [Submodule.mem_torsion_iff]
  refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
  have := congrArg Subtype.val hax
  simpa using this

/-- Si el núcleo es de torsión, `|Tor B| = |ker f| · |Tor A|`. -/
theorem torsion_card_of_surjective (f : B →ₗ[ℤ] A) (hf : Function.Surjective f)
    (hker : LinearMap.ker f ≤ Submodule.torsion ℤ B) :
    Nat.card (Submodule.torsion ℤ B) =
      Nat.card (LinearMap.ker f) * Nat.card (Submodule.torsion ℤ A) := by
  let g : Submodule.torsion ℤ B →ₗ[ℤ] Submodule.torsion ℤ A :=
    (f.domRestrict _).codRestrict _ (fun ⟨b, hb⟩ => by
      obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff b).1 hb
      refine (Submodule.mem_torsion_iff _).2 ⟨n, ?_⟩
      rw [Submonoid.smul_def] at hn ⊢
      simp [← map_smul, hn])
  have hgdef : ∀ x, (g x : A) = f x := fun x => rfl
  have hg : Function.Surjective g := by
    rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := hf a
    obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff _).1 ha
    have hnb : (n : ℤ) • b ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_smul]; rw [Submonoid.smul_def] at hn; exact hn
    obtain ⟨m, hm⟩ := (Submodule.mem_torsion_iff _).1 (hker hnb)
    have hb : b ∈ Submodule.torsion ℤ B :=
      (Submodule.mem_torsion_iff _).2 ⟨m * n, by rw [mul_smul, Submonoid.smul_def n b]; exact hm⟩
    exact ⟨⟨b, hb⟩, rfl⟩
  have hkerg : Nat.card (LinearMap.ker g) = Nat.card (LinearMap.ker f) := by
    refine Nat.card_congr ?_
    exact {
      toFun := fun x => ⟨x.1.1, by
        have h := x.2
        rw [LinearMap.mem_ker] at h
        have := congrArg Subtype.val h
        rw [hgdef] at this
        simpa using this⟩
      invFun := fun y => ⟨⟨y.1, hker y.2⟩, by
        have := y.2; simp only [LinearMap.mem_ker] at this ⊢; ext; simp [hgdef, this]⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have hq := (LinearMap.quotKerEquivOfSurjective g hg).toAddEquiv
  rw [← hkerg, ← Nat.card_congr hq.toEquiv]
  rw [mul_comm]
  exact (LinearMap.ker g).toAddSubgroup.card_eq_card_quotient_mul_card_addSubgroup

/-- **Paso estricto.** Una sobreyección no inyectiva de `ℤ`-módulos finitamente generados
con torsión finita aumenta el rango o, a rango constante, al menos duplica la torsión. -/
theorem strict_step (f : B →ₗ[ℤ] A) (hf : Function.Surjective f) [Module.Finite ℤ B]
    [Finite (Submodule.torsion ℤ B)] (hinj : ¬ Function.Injective f) :
    finrank ℤ A < finrank ℤ B ∨
      (finrank ℤ A = finrank ℤ B ∧
        2 * Nat.card (Submodule.torsion ℤ A) ≤ Nat.card (Submodule.torsion ℤ B)) := by
  have h1 := finrank_eq_add_finrank_ker f hf
  by_cases hr : finrank ℤ A = finrank ℤ B
  · right
    refine ⟨hr, ?_⟩
    have hker := ker_le_torsion_of_finrank_eq f hf hr
    rw [torsion_card_of_surjective f hf hker]
    have hkf : Finite (LinearMap.ker f) :=
      Finite.of_injective (fun x : LinearMap.ker f => (⟨x.1, hker x.2⟩ : Submodule.torsion ℤ B))
        (fun x y h => by simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
    have hk2 : 2 ≤ Nat.card (LinearMap.ker f) := by
      rw [← LinearMap.ker_eq_bot] at hinj
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinj
      have : (1 : ℕ) < Nat.card (LinearMap.ker f) :=
        Finite.one_lt_card_iff_nontrivial.2 ⟨⟨⟨x, hx⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
      omega
    exact Nat.mul_le_mul_right _ hk2
  · left; omega

/-! ## Cuenta de cambios estrictos -/

/-- Potencial `Φ(r, t) = r (⌊log₂ T⌋ + 1) + ⌊log₂ t⌋`. -/
def potential (T r t : ℕ) : ℕ := r * (Nat.log 2 T + 1) + Nat.log 2 t

lemma potential_le {T d r t : ℕ} (hr : r ≤ d) (ht : t ≤ T) :
    potential T r t ≤ d + (d + 1) * Nat.log 2 T := by
  unfold potential
  have h1 : Nat.log 2 t ≤ Nat.log 2 T := Nat.log_mono_right ht
  have h2 : r * (Nat.log 2 T + 1) ≤ d * (Nat.log 2 T + 1) := Nat.mul_le_mul_right _ hr
  nlinarith

lemma potential_strict {T r r' t t' : ℕ} (ht'T : t ≤ T) (ht1 : 1 ≤ t)
    (h : r < r' ∨ (r = r' ∧ 2 * t ≤ t')) : potential T r t < potential T r' t' := by
  unfold potential
  rcases h with h | ⟨rfl, h⟩
  · have h1 : Nat.log 2 t ≤ Nat.log 2 T := Nat.log_mono_right ht'T
    have h2 : (r + 1) * (Nat.log 2 T + 1) ≤ r' * (Nat.log 2 T + 1) :=
      Nat.mul_le_mul_right _ h
    nlinarith
  · have h1 : Nat.log 2 (2 * t) ≤ Nat.log 2 t' := Nat.log_mono_right h
    have h2 : Nat.log 2 (2 * t) = Nat.log 2 t + 1 := by
      rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
    omega

/-- **Cota (L8) de cambios estrictos.** Sea una cadena de invariantes `r k` (rango) y `t k`
(orden de la torsión), `k = 0, …, m`, con `r k ≤ d` y `1 ≤ t k ≤ T`. Si en cada paso
estricto el rango aumenta o, a rango constante, la torsión se multiplica por al menos dos,
y los pasos no estrictos conservan ambos invariantes, entonces el número de pasos estrictos
es a lo sumo `d + (d + 1) ⌊log₂ T⌋`. -/
theorem strict_count_le (r t : ℕ → ℕ) (strict : ℕ → Prop) [DecidablePred strict] (m d T : ℕ)
    (hr : ∀ k ≤ m, r k ≤ d) (ht1 : ∀ k ≤ m, 1 ≤ t k) (htT : ∀ k ≤ m, t k ≤ T)
    (hstrict : ∀ k < m, strict k →
      r k < r (k + 1) ∨ (r k = r (k + 1) ∧ 2 * t k ≤ t (k + 1)))
    (hiso : ∀ k < m, ¬ strict k → r (k + 1) = r k ∧ t (k + 1) = t k) :
    ((Finset.range m).filter strict).card ≤ d + (d + 1) * Nat.log 2 T := by
  have key : ∀ j ≤ m, ((Finset.range j).filter strict).card + potential T (r 0) (t 0) ≤
      potential T (r j) (t j) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hs : strict j
      · rw [if_pos hs, Finset.card_insert_of_notMem (by simp)]
        have := potential_strict (htT j (by omega)) (ht1 j (by omega))
          (hstrict j (by omega) hs)
        omega
      · rw [if_neg hs]
        obtain ⟨h1, h2⟩ := hiso j (by omega) hs
        rw [h1, h2]; exact ih
  have := key m le_rfl
  have := potential_le (hr m le_rfl) (htT m le_rfl) (T := T)
  omega

/-- **Cadena de sobreyecciones (L8)–(L9).** Sea `Q 0 ← Q 1 ← ⋯ ← Q m` una cadena de
sobreyecciones `f k : Q (k+1) ↠ Q k` de grupos abelianos finitamente generados, con rango
`≤ d` y torsión de orden `≤ T`. Entonces a lo sumo `d + (d + 1) ⌊log₂ T⌋` de las
sobreyecciones no son isomorfismos. -/
theorem chain_strict_count (Q : ℕ → Type u) [∀ k, AddCommGroup (Q k)]
    [∀ k, Module.Finite ℤ (Q k)] [∀ k, Finite (Submodule.torsion ℤ (Q k))]
    (f : ∀ k, Q (k + 1) →ₗ[ℤ] Q k) (m d T : ℕ) (hf : ∀ k < m, Function.Surjective (f k))
    (hd : ∀ k ≤ m, finrank ℤ (Q k) ≤ d)
    (hT : ∀ k ≤ m, Nat.card (Submodule.torsion ℤ (Q k)) ≤ T)
    [DecidablePred fun k => ¬ Function.Injective (f k)] :
    ((Finset.range m).filter fun k => ¬ Function.Injective (f k)).card ≤
      d + (d + 1) * Nat.log 2 T := by
  refine strict_count_le (fun k => finrank ℤ (Q k))
    (fun k => Nat.card (Submodule.torsion ℤ (Q k))) _ m d T hd
    (fun k _ => Nat.card_pos) hT (fun k hk hs => ?_) (fun k hk hs => ?_)
  · exact strict_step (f k) (hf k hk) hs
  · push_neg at hs
    have hker : LinearMap.ker (f k) = ⊥ := LinearMap.ker_eq_bot.2 hs
    have e := LinearEquiv.ofBijective (f k) ⟨hs, hf k hk⟩
    refine ⟨e.finrank_eq, ?_⟩
    have := torsion_card_of_surjective (f k) (hf k hk) (by rw [hker]; exact bot_le)
    show Nat.card (Submodule.torsion ℤ (Q (k + 1))) = Nat.card (Submodule.torsion ℤ (Q k))
    rw [this, hker]
    simp

end TypedTriangle.Robust
