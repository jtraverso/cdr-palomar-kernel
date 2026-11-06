/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Orientación euleriana de un multigrafo con grados pares (V11)

Herramienta combinatoria para S26 §4: el emparejamiento, en cada fila, de semiaristas
positivas con negativas equivale a orientar las unidades de modo que en cada fila salgan
tantas como entran. Se demuestra por *splitting-off* (inducción fuerte sobre el número de
unidades), para multiconjuntos de unidades `(etiqueta, extremo₁, extremo₂)` cuyos extremos
se agrupan en filas mediante `ρ : W → R`.

* `exists_euler_orientation`: si cada fila tiene grado par, existe una reorientación
  `O` (cada unidad se conserva o se invierte: `Multiset.Rel Flip M O`) con
  salidas = entradas en cada fila.
* `Rel.map_eq_of_flip_inv`: toda magnitud invariante por inversión se conserva.
-/

open Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace TypedTriangle.EulerOrient

variable {X W R : Type*}

/-- Inversión de una unidad `(etiqueta, extremo₁, extremo₂)`. -/
def flip (u : X × W × W) : X × W × W := (u.1, u.2.2, u.2.1)

@[simp] lemma flip_flip (u : X × W × W) : flip (flip u) = u := rfl

/-- `o` es `u` o su inversión. -/
def Flip (u o : X × W × W) : Prop := o = u ∨ o = flip u

/-- Unidades que salen de la fila `r`. -/
def outC (ρ : W → R) (O : Multiset (X × W × W)) (r : R) : ℕ := O.countP (fun o => ρ o.2.1 = r)

/-- Unidades que entran en la fila `r`. -/
def inC (ρ : W → R) (O : Multiset (X × W × W)) (r : R) : ℕ := O.countP (fun o => ρ o.2.2 = r)

/-- Grado de la fila `r` (los lazos cuentan dos veces). -/
def degC (ρ : W → R) (M : Multiset (X × W × W)) (r : R) : ℕ := outC ρ M r + inC ρ M r

lemma outC_cons (ρ : W → R) (u : X × W × W) (s : Multiset (X × W × W)) (r : R) :
    outC ρ (u ::ₘ s) r = outC ρ s r + if ρ u.2.1 = r then 1 else 0 := by
  unfold outC; rw [Multiset.countP_cons]

lemma inC_cons (ρ : W → R) (u : X × W × W) (s : Multiset (X × W × W)) (r : R) :
    inC ρ (u ::ₘ s) r = inC ρ s r + if ρ u.2.2 = r then 1 else 0 := by
  unfold inC; rw [Multiset.countP_cons]

lemma flip_of_flip {u v : X × W × W} (h : Flip u v) : Flip u (flip v) := by
  rcases h with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (flip_flip u)

/-- **Orientación euleriana.** Si cada fila tiene grado par, las unidades pueden
reorientarse (conservando cada una o invirtiéndola) de modo que en cada fila el número de
unidades salientes sea igual al de entrantes. -/
theorem exists_euler_orientation (ρ : W → R) (M : Multiset (X × W × W))
    (hM : ∀ r, Even (degC ρ M r)) :
    ∃ O, Multiset.Rel Flip M O ∧ ∀ r, outC ρ O r = inC ρ O r := by
  induction h : Multiset.card M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  rcases Multiset.empty_or_exists_mem M with rfl | ⟨e1, he1⟩
  · exact ⟨0, Multiset.Rel.zero, fun r => by simp [outC, inC]⟩
  obtain ⟨Rs, rfl⟩ : ∃ Rs, M = e1 ::ₘ Rs := ⟨_, (Multiset.cons_erase he1).symm⟩
  obtain ⟨x1, a, b⟩ := e1
  have hcard : Multiset.card Rs < n := by rw [← h]; simp
  by_cases hab : ρ a = ρ b
  · -- lazo: se orienta arbitrariamente
    have hRs : ∀ r, Even (degC ρ Rs r) := by
      intro r
      have := hM r
      unfold degC at this ⊢
      rw [outC_cons, inC_cons] at this
      simp only at this
      rw [hab] at this
      split_ifs at this
      · have h2 : outC ρ Rs r + 1 + (inC ρ Rs r + 1) = outC ρ Rs r + inC ρ Rs r + 2 := by ring
        rw [h2, Nat.even_add] at this
        exact this.mpr (by decide)
      · simpa using this
    obtain ⟨O, hrel, hbal⟩ := ih _ hcard Rs hRs rfl
    refine ⟨(x1, a, b) ::ₘ O, Multiset.Rel.cons (Or.inl rfl) hrel, fun r => ?_⟩
    rw [outC_cons, inC_cons, hbal r]
    simp only [hab]
  · -- la fila de `b` tiene grado impar en `Rs`: hay otra unidad en ella
    have hodd : 0 < degC ρ Rs (ρ b) := by
      have := hM (ρ b)
      unfold degC at this ⊢
      rw [outC_cons, inC_cons] at this
      simp only [hab, if_false, if_true] at this
      by_contra hc
      have h1 : outC ρ Rs (ρ b) = 0 := by omega
      have h2 : inC ρ Rs (ρ b) = 0 := by omega
      rw [h1, h2] at this
      exact Nat.not_even_one this
    have hex : ∃ e2b, ∃ e2 ∈ Rs, Flip e2 e2b ∧ ρ e2b.2.1 = ρ b := by
      unfold degC outC inC at hodd
      rcases Nat.eq_zero_or_pos (Multiset.countP (fun o : X × W × W => ρ o.2.1 = ρ b) Rs)
        with h0 | h0
      · rw [h0, zero_add] at hodd
        obtain ⟨e2, he2, hq⟩ := Multiset.countP_pos.mp hodd
        exact ⟨flip e2, e2, he2, Or.inr rfl, hq⟩
      · obtain ⟨e2, he2, hq⟩ := Multiset.countP_pos.mp h0
        exact ⟨e2, e2, he2, Or.inl rfl, hq⟩
    obtain ⟨⟨x2, b', c⟩, e2, he2, hfl, hb'⟩ := hex
    simp only at hb'
    obtain ⟨Rs', rfl⟩ : ∃ Rs', Rs = e2 ::ₘ Rs' := ⟨_, (Multiset.cons_erase he2).symm⟩
    have hdeg2 : ∀ r, (if ρ e2.2.1 = r then 1 else 0) + (if ρ e2.2.2 = r then 1 else 0) =
        (if ρ b' = r then 1 else 0) + (if ρ c = r then (1 : ℕ) else 0) := by
      intro r
      rcases hfl with h' | h'
      · subst h'; rfl
      · have h'' : e2 = flip (x2, b', c) := by rw [h']; rfl
        subst h''
        change (if ρ c = r then 1 else 0) + (if ρ b' = r then 1 else 0) =
          (if ρ b' = r then 1 else 0) + (if ρ c = r then (1 : ℕ) else 0)
        exact Nat.add_comm _ _
    have hM2 : ∀ r, Even (degC ρ ((x1, a, c) ::ₘ Rs') r) := by
      intro r
      have := hM r
      have h2 := hdeg2 r
      unfold degC at this ⊢
      rw [outC_cons, inC_cons, outC_cons, inC_cons] at this
      rw [outC_cons, inC_cons]
      simp only at this ⊢
      rw [hb'] at h2
      have key : outC ρ Rs' r + (if ρ e2.2.1 = r then 1 else 0) + (if ρ a = r then 1 else 0) +
          (inC ρ Rs' r + (if ρ e2.2.2 = r then 1 else 0) + (if ρ b = r then 1 else 0)) =
          outC ρ Rs' r + (if ρ a = r then 1 else 0) + (inC ρ Rs' r + (if ρ c = r then 1 else 0))
            + 2 * (if ρ b = r then 1 else 0) := by
        split_ifs at h2 ⊢ <;> omega
      rw [key, Nat.even_add] at this
      exact this.mpr (even_two_mul _)
    have hcard2 : Multiset.card ((x1, a, c) ::ₘ Rs') < n := by rw [← h]; simp
    obtain ⟨O2, hrel2, hbal2⟩ := ih _ hcard2 _ hM2 rfl
    obtain ⟨o, O2', ho, hrel', rfl⟩ := Multiset.rel_cons_left.mp hrel2
    rcases ho with rfl | rfl
    · refine ⟨(x1, a, b) ::ₘ (x2, b', c) ::ₘ O2',
        Multiset.Rel.cons (Or.inl rfl) (Multiset.Rel.cons hfl hrel'), fun r => ?_⟩
      have := hbal2 r
      rw [outC_cons, inC_cons] at this
      change outC ρ O2' r + (if ρ a = r then 1 else 0) =
        inC ρ O2' r + (if ρ c = r then 1 else 0) at this
      rw [outC_cons, outC_cons, inC_cons, inC_cons]
      simp only [hb'] at this ⊢
      split_ifs at this ⊢ <;> omega
    · refine ⟨(x1, b, a) ::ₘ (x2, c, b') ::ₘ O2',
        Multiset.Rel.cons (Or.inr rfl) (Multiset.Rel.cons (flip_of_flip hfl) hrel'),
        fun r => ?_⟩
      have := hbal2 r
      rw [outC_cons, inC_cons] at this
      change outC ρ O2' r + (if ρ c = r then 1 else 0) =
        inC ρ O2' r + (if ρ a = r then 1 else 0) at this
      rw [outC_cons, outC_cons, inC_cons, inC_cons]
      simp only [flip, hb'] at this ⊢
      split_ifs at this ⊢ <;> omega

/-- Toda magnitud invariante por inversión se conserva al reorientar. -/
theorem Rel.map_eq_of_flip_inv {Y : Type*} {M O : Multiset (X × W × W)}
    (h : Multiset.Rel Flip M O) (g : X × W × W → Y) (hg : ∀ u ∈ M, g (flip u) = g u) :
    O.map g = M.map g := by
  induction h with
  | zero => rfl
  | @cons u o as bs huo _ ih =>
    rw [Multiset.map_cons, Multiset.map_cons,
      ih (fun v hv => hg v (Multiset.mem_cons_of_mem hv))]
    rcases huo with rfl | rfl
    · rfl
    · rw [hg u (Multiset.mem_cons_self _ _)]

/-- Toda unidad reorientada procede de una unidad original. -/
theorem Rel.exists_of_mem {M O : Multiset (X × W × W)} (h : Multiset.Rel Flip M O)
    {o : X × W × W} (ho : o ∈ O) : ∃ u ∈ M, Flip u o := by
  induction h with
  | zero => simp at ho
  | @cons u o' as bs huo _ ih =>
    rcases Multiset.mem_cons.mp ho with rfl | hm
    · exact ⟨u, Multiset.mem_cons_self _ _, huo⟩
    · obtain ⟨v, hv, hvo⟩ := ih hm
      exact ⟨v, Multiset.mem_cons_of_mem hv, hvo⟩

/-- Los extremos (como multiconjunto de pares extremo/etiqueta) se conservan. -/
theorem Rel.endpoint_count {M O : Multiset (X × W × W)} (h : Multiset.Rel Flip M O)
    (q : W → Prop) :
    O.countP (fun o => q o.2.1) + O.countP (fun o => q o.2.2) =
      M.countP (fun o => q o.2.1) + M.countP (fun o => q o.2.2) := by
  induction h with
  | zero => rfl
  | @cons u o as bs huo _ ih =>
    have hunit : (if q o.2.1 then 1 else 0) + (if q o.2.2 then 1 else 0) =
        (if q u.2.1 then 1 else 0) + (if q u.2.2 then (1 : ℕ) else 0) := by
      rcases huo with rfl | rfl
      · rfl
      · change (if q u.2.2 then 1 else 0) + (if q u.2.1 then 1 else 0) = _
        exact Nat.add_comm _ _
    simpa only [Multiset.countP_cons, add_assoc, add_left_comm, add_comm] using
      congrArg₂ (fun a b : ℕ => a + b) ih hunit

end TypedTriangle.EulerOrient
