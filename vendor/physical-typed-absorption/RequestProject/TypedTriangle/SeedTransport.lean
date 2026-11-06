/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Seed
public import RequestProject.TypedTriangle.RobustHinge
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# B1 — Transporte de semilla con pivotes promediados compartidos y soporte residual

Generaliza `transport_identity` (pivotes deterministas) a núcleos de pivotes reales
`p f : Finset V → ℝ` (por ejemplo, la ley de un pivote aleatorio `P_f` de la arista borrada
`f`), compartidos por todos los certificados:

* `transport_identity_avg`: si `∂ cert_T = 1_T − Σ_{f ∈ E(T) ∩ B} ∂ p_f`, entonces
  `∂ψ = ∂μ − 1_B − Σ_{f ∈ B} (∂μ f − 1) ∂p_f` (no se requiere normalización de `p_f`);
* `pivot_mass_local`: si `p_f ≥ 0`, `p_f ≤ κ/n` y `p_f` está soportado en triángulos que
  contienen `f`, entonces en cada arista superviviente `e`,
  `Σ_{f ∈ B} ∂p_f(e) ≤ 2 κ d / n` (grado de `B` ≤ `d`);
* `transport_error_avg_local`: `|∂ψ e − 1| ≤ (1 + 2κd/n) ε` en las aristas supervivientes;
* `transported_support` y `bdry_subHost_eq`: si los certificados están soportados en
  triángulos del residual `J = E ∖ B`, también lo está `ψ`, y su borde en el host residual
  coincide con su borde en `H`.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-- Término de pivotes promediados: `Σ_{f ∈ B} 1_{E(T)}(f) · ∂p_f(e)`. -/
def pivotTermW (H : Host V I) (F : Set (Multiset I)) (Fst : Finset (Sym2 V))
    (p : Sym2 V → Finset V → ℝ) (T : Finset V) (e : Sym2 V) : ℝ :=
  ∑ f ∈ Fst, indR (triEdges T) f * bdry H F (p f) e

/-- **Identidad exacta del transporte con pivotes promediados (B1).** -/
theorem transport_identity_avg {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ}
    {Fst : Finset (Sym2 V)} {D : Finset (Finset V)} (hD : IsDecomposition H F Fst D)
    (p : Sym2 V → Finset V → ℝ) (cert : Finset V → Finset V → ℝ)
    (hcert : ∀ T ∈ allowed H F, ∀ e,
      bdry H F (cert T) e = indR (triEdges T) e - pivotTermW H F Fst p T e)
    (e : Sym2 V) :
    bdry H F (transported H F μ D cert) e =
      bdry H F μ e - indR Fst e - ∑ f ∈ Fst, (bdry H F μ f - 1) * bdry H F (p f) e := by
  have hDA : ∀ T ∈ D, T ∈ allowed H F := fun T hT => by
    simpa [allowed] using hD.1 T hT
  have hlin : bdry H F (transported H F μ D cert) e =
      ∑ T ∈ allowed H F, μ T * bdry H F (cert T) e - ∑ T ∈ D, bdry H F (cert T) e := by
    unfold bdry transported
    simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun S _ => by ring
    · rw [Finset.sum_comm]
  rw [hlin]
  have h1 : ∑ T ∈ allowed H F, μ T * bdry H F (cert T) e =
      bdry H F μ e - ∑ f ∈ Fst, bdry H F μ f * bdry H F (p f) e := by
    rw [Finset.sum_congr rfl fun T hT => by rw [hcert T hT e]]
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    unfold pivotTermW
    conv_rhs => rw [Finset.sum_congr rfl fun f _ => by rw [bdry]]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun T _ => by ring
  have h2 : ∑ T ∈ D, bdry H F (cert T) e =
      indR Fst e - ∑ f ∈ Fst, bdry H F (p f) e := by
    rw [Finset.sum_congr rfl fun T hT => by rw [hcert T (hDA T hT) e]]
    rw [Finset.sum_sub_distrib, sum_indR_of_isDecomposition hD e]
    congr 1
    unfold pivotTermW
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [← Finset.sum_mul, sum_indR_of_isDecomposition hD f]
    simp [indR, hf]
  rw [h1, h2]
  simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

/-- **Error con pivotes promediados.** Si `∂μ = 1 + r` con `|r| ≤ ε` en las aristas, en cada
arista superviviente `e`, `|∂ψ e − 1| ≤ (1 + Σ_{f∈B} |∂p_f(e)|) ε`. -/
theorem transport_error_avg {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ}
    {r : Sym2 V → ℝ} (hμ : ∀ f ∈ edges H, bdry H F μ f = 1 + r f) {ε : ℝ}
    (hr : ∀ f ∈ edges H, |r f| ≤ ε)
    {Fst : Finset (Sym2 V)} {D : Finset (Finset V)} (hD : IsDecomposition H F Fst D)
    (hFst : Fst ⊆ edges H) (p : Sym2 V → Finset V → ℝ) (cert : Finset V → Finset V → ℝ)
    (hcert : ∀ T ∈ allowed H F, ∀ e,
      bdry H F (cert T) e = indR (triEdges T) e - pivotTermW H F Fst p T e)
    {e : Sym2 V} (he : e ∈ edges H) (heF : e ∉ Fst) :
    |bdry H F (transported H F μ D cert) e - 1| ≤
      (1 + ∑ f ∈ Fst, |bdry H F (p f) e|) * ε := by
  rw [transport_identity_avg hD p cert hcert e, hμ e he]
  rw [Finset.sum_congr rfl fun f hf => by rw [hμ f (hFst hf)]]
  simp only [indR, if_neg heF, sub_zero, add_sub_cancel_left]
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hr e he)
  have hsum : |∑ f ∈ Fst, r f * bdry H F (p f) e| ≤ (∑ f ∈ Fst, |bdry H F (p f) e|) * ε := by
    calc |∑ f ∈ Fst, r f * bdry H F (p f) e|
        ≤ ∑ f ∈ Fst, |r f * bdry H F (p f) e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ f ∈ Fst, |bdry H F (p f) e| * ε := by
          refine Finset.sum_le_sum fun f hf => ?_
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_left (hr f (hFst hf)) (abs_nonneg _)
      _ = (∑ f ∈ Fst, |bdry H F (p f) e|) * ε := by rw [Finset.sum_mul]
  calc |1 + r e - ∑ x ∈ Fst, r x * bdry H F (p x) e - 1|
      = |r e - ∑ f ∈ Fst, r f * bdry H F (p f) e| := by congr 1; ring
    _ ≤ |r e| + |∑ f ∈ Fst, r f * bdry H F (p f) e| := abs_sub _ _
    _ ≤ ε + (∑ f ∈ Fst, |bdry H F (p f) e|) * ε := add_le_add (hr e he) hsum
    _ = (1 + ∑ f ∈ Fst, |bdry H F (p f) e|) * ε := by ring

omit [Fintype V] in
lemma toFinset_subset_of_mem_triEdges {T : Finset V} {e : Sym2 V} (he : e ∈ triEdges T) :
    e.toFinset ⊆ T := fun _ hx => mem_of_mem_triEdges he (Sym2.mem_toFinset.1 hx)

omit [Fintype V] in
lemma eq_of_toFinset_eq {e f : Sym2 V} (h : e.toFinset = f.toFinset) : e = f :=
  Sym2.ext fun x => by rw [← Sym2.mem_toFinset, h, Sym2.mem_toFinset]

/-- Un triángulo de tamaño 3 que contiene dos aristas distintas `e, f` es `e ∪ f`; si `e` y
`f` no comparten vértice no existe tal triángulo. -/
lemma tri_unique_of_two_edges {H : Host V I} {F : Set (Multiset I)} {e f : Sym2 V}
    (hef : e ≠ f) (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag) {T : Finset V}
    (hT : T ∈ allowed H F) (heT : e ∈ triEdges T) (hfT : f ∈ triEdges T) :
    T = e.toFinset ∪ f.toFinset ∧ (e.toFinset ∩ f.toFinset).Nonempty := by
  have hT3 : T.card = 3 := (Finset.mem_filter.1 hT).2.1
  have hsub : e.toFinset ∪ f.toFinset ⊆ T :=
    Finset.union_subset (toFinset_subset_of_mem_triEdges heT) (toFinset_subset_of_mem_triEdges hfT)
  have he2 := Sym2.card_toFinset_of_not_isDiag e he
  have hf2 := Sym2.card_toFinset_of_not_isDiag f hf
  have hge : 3 ≤ (e.toFinset ∪ f.toFinset).card := by
    by_contra hlt
    push_neg at hlt
    have h1 : e.toFinset = e.toFinset ∪ f.toFinset := Finset.eq_of_subset_of_card_le
      Finset.subset_union_left (by omega)
    have h2 : f.toFinset = e.toFinset ∪ f.toFinset := Finset.eq_of_subset_of_card_le
      Finset.subset_union_right (by omega)
    exact hef (eq_of_toFinset_eq (h1.trans h2.symm))
  have hTeq : T = e.toFinset ∪ f.toFinset :=
    (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  refine ⟨hTeq, ?_⟩
  rw [Finset.nonempty_iff_ne_empty]
  intro hint
  have := Finset.card_union_add_card_inter e.toFinset f.toFinset
  rw [hint, Finset.card_empty] at this
  have := Finset.card_le_card hsub
  omega

/-- **Localidad de la masa de pivotes (B1).** Si cada núcleo `p_f` es no negativo, acotado por
`κ/n` y soportado en triángulos permitidos que contienen `f`, y `B` tiene grado `≤ d`,
entonces en cada arista `e ∉ B`, `Σ_{f ∈ B} ∂p_f(e) ≤ 2 d κ / n`. -/
theorem pivot_mass_local {H : Host V I} {F : Set (Multiset I)} {Fst : Finset (Sym2 V)}
    (hFst : Fst ⊆ edges H) {d : ℕ} (hdeg : ∀ x, degIn Fst x ≤ d)
    (p : Sym2 V → Finset V → ℝ) {κ : ℝ} (hp0 : ∀ f T, 0 ≤ p f T)
    (hpκ : ∀ f T, p f T ≤ κ / Fintype.card V)
    (hpsupp : ∀ f T, p f T ≠ 0 → f ∈ triEdges T) {e : Sym2 V} (he : ¬ e.IsDiag)
    (heF : e ∉ Fst) :
    ∑ f ∈ Fst, bdry H F (p f) e ≤ 2 * d * (κ / Fintype.card V) := by
  have hκ : ∀ f, 0 ≤ κ / Fintype.card V := fun f => (hp0 f ∅).trans (hpκ f ∅)
  set share : Sym2 V → Prop := fun f => (e.toFinset ∩ f.toFinset).Nonempty
  have hone : ∀ f ∈ Fst, bdry H F (p f) e ≤ if share f then κ / Fintype.card V else 0 := by
    intro f hf
    have hfnd : ¬ f.IsDiag := by
      have := hFst hf
      simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact H.G.not_isDiag_of_mem_edgeSet this
    have hef : e ≠ f := fun h => heF (h ▸ hf)
    rw [bdry_eq_sum_triOn, ← Finset.sum_filter_add_sum_filter_not (triOn H F e)
      (fun T => f ∈ triEdges T)]
    have hzero : ∑ T ∈ (triOn H F e).filter (fun T => ¬ f ∈ triEdges T), p f T = 0 :=
      Finset.sum_eq_zero fun T hT => by
        by_contra h0; exact (Finset.mem_filter.1 hT).2 (hpsupp f T h0)
    rw [hzero, add_zero]
    have hcard : ((triOn H F e).filter (fun T => f ∈ triEdges T)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro T hT T' hT'
      simp only [Finset.mem_filter, triOn] at hT hT'
      rw [(tri_unique_of_two_edges hef he hfnd hT.1.1 hT.1.2 hT.2).1,
        (tri_unique_of_two_edges hef he hfnd hT'.1.1 hT'.1.2 hT'.2).1]
    split_ifs with hsh
    · calc ∑ T ∈ (triOn H F e).filter (fun T => f ∈ triEdges T), p f T
          ≤ ∑ _T ∈ (triOn H F e).filter (fun T => f ∈ triEdges T), κ / Fintype.card V :=
            Finset.sum_le_sum fun T _ => hpκ f T
        _ = ((triOn H F e).filter (fun T => f ∈ triEdges T)).card * (κ / Fintype.card V) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 1 * (κ / Fintype.card V) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hκ f)
        _ = κ / Fintype.card V := one_mul _
    · refine le_of_eq (Finset.sum_eq_zero fun T hT => ?_)
      simp only [Finset.mem_filter, triOn] at hT
      exact absurd (tri_unique_of_two_edges hef he hfnd hT.1.1 hT.1.2 hT.2).2 hsh
  calc ∑ f ∈ Fst, bdry H F (p f) e
      ≤ ∑ f ∈ Fst, (if share f then κ / Fintype.card V else 0) := Finset.sum_le_sum hone
    _ = (Fst.filter share).card * (κ / Fintype.card V) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * d : ℕ) * (κ / Fintype.card V) := by
        refine mul_le_mul_of_nonneg_right ?_ (hκ e)
        have hsub : Fst.filter share ⊆ e.toFinset.biUnion (fun x => Fst.filter (fun f => x ∈ f)) := by
          intro f hf
          rw [Finset.mem_filter] at hf
          obtain ⟨x, hx⟩ := hf.2
          rw [Finset.mem_inter, Sym2.mem_toFinset, Sym2.mem_toFinset] at hx
          exact Finset.mem_biUnion.2 ⟨x, Sym2.mem_toFinset.2 hx.1, Finset.mem_filter.2 ⟨hf.1, hx.2⟩⟩
        have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
        have h2 : ∑ x ∈ e.toFinset, (Fst.filter (fun f => x ∈ f)).card ≤ ∑ _x ∈ e.toFinset, d :=
          Finset.sum_le_sum fun x _ => hdeg x
        rw [Finset.sum_const, smul_eq_mul, Sym2.card_toFinset_of_not_isDiag e he] at h2
        exact_mod_cast h1.trans h2
    _ = 2 * d * (κ / Fintype.card V) := by push_cast; ring

/-- **(L14) con pivotes promediados locales.** Combinación de `transport_error_avg` y
`pivot_mass_local`: en cada arista superviviente, `|∂ψ e − 1| ≤ (1 + 2dκ/n) ε`. No aparece un
error aditivo independiente de `ε`. -/
theorem transport_error_avg_local {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ}
    {r : Sym2 V → ℝ} (hμ : ∀ f ∈ edges H, bdry H F μ f = 1 + r f) {ε : ℝ}
    (hr : ∀ f ∈ edges H, |r f| ≤ ε)
    {Fst : Finset (Sym2 V)} {D : Finset (Finset V)} (hD : IsDecomposition H F Fst D)
    (hFst : Fst ⊆ edges H) {d : ℕ} (hdeg : ∀ x, degIn Fst x ≤ d)
    (p : Sym2 V → Finset V → ℝ) {κ : ℝ} (hp0 : ∀ f T, 0 ≤ p f T)
    (hpκ : ∀ f T, p f T ≤ κ / Fintype.card V)
    (hpsupp : ∀ f T, p f T ≠ 0 → f ∈ triEdges T) (cert : Finset V → Finset V → ℝ)
    (hcert : ∀ T ∈ allowed H F, ∀ e,
      bdry H F (cert T) e = indR (triEdges T) e - pivotTermW H F Fst p T e)
    {e : Sym2 V} (he : e ∈ edges H) (heF : e ∉ Fst) :
    |bdry H F (transported H F μ D cert) e - 1| ≤
      (1 + 2 * d * (κ / Fintype.card V)) * ε := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hr e he)
  have hend : ¬ e.IsDiag := by
    simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact H.G.not_isDiag_of_mem_edgeSet he
  have hb0 : ∀ f, 0 ≤ bdry H F (p f) e := fun f => by
    rw [bdry_eq_sum_triOn]; exact Finset.sum_nonneg fun T _ => hp0 f T
  refine (transport_error_avg hμ hr hD hFst p cert hcert he heF).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hε
  have := pivot_mass_local (H := H) (F := F) hFst hdeg p hp0 hpκ hpsupp hend heF
  rw [Finset.sum_congr rfl fun f _ => abs_of_nonneg (hb0 f)]
  linarith

/-- Host residual `J = E ∖ B`. -/
def residual (H : Host V I) (Fst : Finset (Sym2 V)) : Host V I := subHost H (edges H \ Fst)

/-- **Soporte residual.** Si cada certificado está soportado en triángulos permitidos del
residual, también lo está el peso transportado `ψ`. -/
theorem transported_support {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ}
    {Fst : Finset (Sym2 V)} {D : Finset (Finset V)} (hD : IsDecomposition H F Fst D)
    (cert : Finset V → Finset V → ℝ)
    (hsupp : ∀ T ∈ allowed H F, ∀ S, cert T S ≠ 0 → IsAllowed (residual H Fst) F S)
    (S : Finset V) (hS : transported H F μ D cert S ≠ 0) : IsAllowed (residual H Fst) F S := by
  by_contra hnot
  apply hS
  unfold transported
  have h1 : ∀ T ∈ allowed H F, cert T S = 0 := fun T hT => by
    by_contra h; exact hnot (hsupp T hT S h)
  rw [Finset.sum_eq_zero fun T hT => by rw [h1 T hT, mul_zero],
    Finset.sum_eq_zero fun T hT => h1 T (by simpa [allowed] using hD.1 T hT), sub_zero]

/-- El borde en el host residual de un peso soportado en triángulos residuales coincide con
su borde en `H`. -/
theorem bdry_residual_eq {H : Host V I} {F : Set (Multiset I)} {Fst : Finset (Sym2 V)}
    (w : Finset V → ℝ) (hw : ∀ S, w S ≠ 0 → IsAllowed (residual H Fst) F S) (e : Sym2 V) :
    bdry (residual H Fst) F w e = bdry H F w e := by
  unfold bdry
  refine Finset.sum_subset ?_ ?_
  · intro S hS
    simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact isAllowed_mono (subHost_le H _) rfl hS
  · intro S _ hS
    have : w S = 0 := by
      by_contra h
      exact hS (by simpa [allowed] using hw S h)
    rw [this, zero_mul]

/-- **Identidad del transporte en el residual (B1, forma de la guía).** Con pivotes
promediados compartidos y certificados soportados en el residual `J = E ∖ B`,
`A_J ψ − 1_J = r|_J − Σ_{f ∈ B} r_f (A_H p_f)|_J`. -/
theorem transport_identity_residual {H : Host V I} {F : Set (Multiset I)} {μ : Finset V → ℝ}
    {r : Sym2 V → ℝ} (hμ : ∀ f ∈ edges H, bdry H F μ f = 1 + r f)
    {Fst : Finset (Sym2 V)} {D : Finset (Finset V)} (hD : IsDecomposition H F Fst D)
    (hFst : Fst ⊆ edges H) (p : Sym2 V → Finset V → ℝ) (cert : Finset V → Finset V → ℝ)
    (hcert : ∀ T ∈ allowed H F, ∀ e,
      bdry H F (cert T) e = indR (triEdges T) e - pivotTermW H F Fst p T e)
    (hsupp : ∀ T ∈ allowed H F, ∀ S, cert T S ≠ 0 → IsAllowed (residual H Fst) F S)
    {e : Sym2 V} (he : e ∈ edges H) (heF : e ∉ Fst) :
    bdry (residual H Fst) F (transported H F μ D cert) e - 1 =
      r e - ∑ f ∈ Fst, r f * bdry H F (p f) e := by
  rw [bdry_residual_eq _ (transported_support hD cert hsupp) e,
    transport_identity_avg hD p cert hcert e, hμ e he]
  rw [Finset.sum_congr rfl fun f hf => by rw [hμ f (hFst hf)]]
  simp only [indR, if_neg heF, add_sub_cancel_left]
  ring

end TypedTriangle
