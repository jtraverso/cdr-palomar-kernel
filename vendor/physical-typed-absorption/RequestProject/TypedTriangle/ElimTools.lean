/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.G1ZSplice

@[expose] public section

/-!
# G1-Z, §6 de la guía V5 — Herramientas de la eliminación lineal

Dos tipos de eventos, ambos homomorfismos fijados ANTES de la demanda:

* **Evento de pivotes** (`pivC`, `pivF`): para un conjunto `S` de aristas y pivotes `p(e)`
  (triángulos permitidos con `e ∈ E(p(e))` y sin otra arista de `S`), se resta `x_e` veces
  `𝟏_{E(p(e))}`. Anula las coordenadas de `S`, cuesta `≤ ‖x‖₁` y la norma residual es
  `≤ 4‖x‖₁`. Es lineal en TODO `ℤ^E`.
* **Evento de estrellas** (`star_event`): para un conjunto `R` de raíces y grafos
  `G_v ≤ L_v` de diámetro `≤ D` cuyas bases evitan `R`, se restan simultáneamente las
  soluciones de las secciones lineales de las estrellas. Anula todas las estrellas de `R`,
  con coste `≤ (2D+1)·2‖x‖₁` (cada arista está en dos estrellas): sin factor `n`. Es lineal
  en el submódulo donde las estrellas están en las imágenes enteras de los `G_v`.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence

variable {V I : Type*} [Fintype V]

/-! ## Cotas generales -/

lemma l1E_triBd_le (H : Host V I) (F : Set (Multiset I)) (c : Finset V → ℤ) :
    l1E (triBd H F c) ≤ 3 * ∑ T, |c T| := by
  change l1E (∑ T ∈ allowed H F, c T • ind (triEdges T)) ≤ _
  refine (l1E_sum_le _ _).trans ?_
  calc ∑ T ∈ allowed H F, l1E (c T • ind (triEdges T))
      = ∑ T ∈ allowed H F, |c T| * 3 := Finset.sum_congr rfl fun T hT => by
        rw [l1E_smul, l1E_ind_triEdges (Finset.mem_filter.1 hT).2.1]
    _ ≤ ∑ T, |c T| * 3 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => by positivity
    _ = 3 * ∑ T, |c T| := by rw [← Finset.sum_mul, mul_comm]

lemma triBd_mem_localGroup (H : Host V I) (F : Set (Multiset I)) (c : Finset V → ℤ) :
    triBd H F c ∈ localGroup H F := by
  refine Submodule.sum_mem _ fun T hT => Submodule.smul_mem _ _ ?_
  exact lattice_le_localGroup H F (Submodule.subset_span ⟨T, (Finset.mem_filter.1 hT).2, rfl⟩)

lemma triBd_apply (H : Host V I) (F : Set (Multiset I)) (c : Finset V → ℤ) (e : Sym2 V) :
    triBd H F c e = ∑ T ∈ allowed H F, c T * ind (triEdges T) e := by
  change (∑ T ∈ allowed H F, c T • ind (triEdges T)) e = _
  simp [Finset.sum_apply]

/-- Soporte de `A c`: una arista con valor no nulo está en un triángulo del soporte de `c`. -/
lemma triBd_support {H : Host V I} {F : Set (Multiset I)} {c : Finset V → ℤ} {e : Sym2 V}
    (he : triBd H F c e ≠ 0) : ∃ T ∈ allowed H F, c T ≠ 0 ∧ e ∈ triEdges T := by
  rw [triBd_apply] at he
  obtain ⟨T, hT, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  refine ⟨T, hT, fun h => hne (by simp [h]), ?_⟩
  by_contra h; exact hne (by simp [ind, h])

/-- En `M_H`, una arista sin triángulo permitido tiene coordenada nula. -/
lemma localGroup_apply_eq_zero {H : Host V I} {F : Set (Multiset I)} {x : Sym2 V → ℤ}
    (hx : x ∈ localGroup H F) {u v : V} (huv : u ≠ v)
    (hno : ∀ T, IsAllowed H F T → u ∈ T → v ∉ T) : x s(u, v) = 0 := by
  obtain ⟨c, hc⟩ := hx.2 u
  rw [hc v (Ne.symm huv)]
  refine Finset.sum_eq_zero fun T hT => ?_
  obtain ⟨hT1, hvT⟩ := Finset.mem_filter.1 hT
  obtain ⟨hTa, huT⟩ := mem_triAt.1 hT1
  exact absurd hvT (hno T hTa huT)

/-- Cada arista está en a lo sumo dos estrellas: `Σ_{v ∈ R} ‖π_v x‖₁ ≤ 2‖x‖₁`. -/
lemma sum_l1V_starProj_le (R : Finset V) (x : Sym2 V → ℤ) :
    ∑ v ∈ R, l1V (starProj v x) ≤ 2 * l1E x := by
  have h1 : ∑ v ∈ R, l1V (starProj v x) ≤ ∑ p : V × V, |x (Sym2.mk p.1 p.2)| := by
    calc ∑ v ∈ R, l1V (starProj v x)
        ≤ ∑ v, l1V (starProj v x) := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) fun v _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
      _ ≤ ∑ v, ∑ w, |x s(v, w)| := Finset.sum_le_sum fun v _ =>
          Finset.sum_le_sum fun w _ => by
            rw [starProj_apply]; split_ifs <;> simp
      _ = ∑ p : V × V, |x (Sym2.mk p.1 p.2)| := by rw [← Finset.sum_product']; rfl
  have h2 : ∑ p : V × V, |x (Sym2.mk p.1 p.2)| ≤ 2 * l1E x := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := fun p : V × V => Sym2.mk p.1 p.2)
      (fun _ _ => Finset.mem_univ _), l1E, Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    have hfib : (univ.filter (fun p : V × V => Sym2.mk p.1 p.2 = e)).card ≤ 2 := by
      induction e using Sym2.ind with
      | _ a b =>
      refine (Finset.card_le_card (t := {(a, b), (b, a)}) ?_).trans Finset.card_le_two
      intro p hp
      have := (Finset.mem_filter.1 hp).2
      obtain ⟨p1, p2⟩ := p
      change s(p1, p2) = s(a, b) at this
      rcases Sym2.eq_iff.1 this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
    calc ∑ p ∈ univ.filter (fun p : V × V => Sym2.mk p.1 p.2 = e), |x (Sym2.mk p.1 p.2)|
        = ∑ p ∈ univ.filter (fun p : V × V => Sym2.mk p.1 p.2 = e), |x e| :=
          Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.1 hp).2]
      _ = (univ.filter (fun p : V × V => Sym2.mk p.1 p.2 = e)).card * |x e| := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * |x e| := by
          have : ((univ.filter (fun p : V × V => Sym2.mk p.1 p.2 = e)).card : ℤ) ≤ 2 := by
            exact_mod_cast hfib
          nlinarith [abs_nonneg (x e)]
  linarith

/-! ## Evento de pivotes -/

/-- Sistema de pivotes para un conjunto de aristas `S`. -/
structure PivotSys (H : Host V I) (F : Set (Multiset I)) (S : Finset (Sym2 V)) where
  piv : Sym2 V → Finset V
  allowed : ∀ e ∈ S, piv e ∈ allowed H F
  mem : ∀ e ∈ S, e ∈ triEdges (piv e)
  uniq : ∀ e ∈ S, ∀ e' ∈ S, e' ∈ triEdges (piv e) → e' = e

variable {H : Host V I} {F : Set (Multiset I)} {S : Finset (Sym2 V)}

/-- Coeficientes del evento de pivotes. -/
def pivC (ps : PivotSys H F S) : (Sym2 V → ℤ) →ₗ[ℤ] (Finset V → ℤ) where
  toFun x := ∑ e ∈ S, x e • Pi.single (ps.piv e) 1
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' k x := by simp [Finset.smul_sum, mul_smul]

lemma triBd_pivC (ps : PivotSys H F S) (x : Sym2 V → ℤ) :
    triBd H F (pivC ps x) = ∑ e ∈ S, x e • ind (triEdges (ps.piv e)) := by
  change triBd H F (∑ e ∈ S, x e • Pi.single (ps.piv e) 1) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun e he => by rw [map_zsmul, triBd_single (ps.allowed e he)]

lemma sum_abs_pivC_le (ps : PivotSys H F S) (x : Sym2 V → ℤ) :
    ∑ T, |pivC ps x T| ≤ l1E x := by
  change ∑ T, |(∑ e ∈ S, x e • (Pi.single (ps.piv e) 1 : Finset V → ℤ)) T| ≤ _
  calc ∑ T, |(∑ e ∈ S, x e • (Pi.single (ps.piv e) 1 : Finset V → ℤ)) T|
      ≤ ∑ T, ∑ e ∈ S, |x e| * |(Pi.single (ps.piv e) 1 : Finset V → ℤ) T| := by
        refine Finset.sum_le_sum fun T _ => ?_
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp [abs_mul]
    _ = ∑ e ∈ S, |x e| * ∑ T, |(Pi.single (ps.piv e) 1 : Finset V → ℤ) T| := by
        rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ = ∑ e ∈ S, |x e| := Finset.sum_congr rfl fun e _ => by
        rw [Finset.sum_eq_single (ps.piv e)]
        · simp
        · intro b _ hb; simp [hb]
        · simp
    _ ≤ l1E x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => abs_nonneg _

/-- Residuo del evento de pivotes. -/
def pivF (ps : PivotSys H F S) (x : Sym2 V → ℤ) : Sym2 V → ℤ := x - triBd H F (pivC ps x)

lemma pivF_apply_mem (ps : PivotSys H F S) (x : Sym2 V → ℤ) {e' : Sym2 V} (he' : e' ∈ S) :
    pivF ps x e' = 0 := by
  rw [pivF, Pi.sub_apply, triBd_pivC, Finset.sum_apply, Finset.sum_eq_single e']
  · simp [ind, ps.mem e' he']
  · intro b hb hne
    simp only [Pi.smul_apply, ind, smul_eq_mul]
    rw [if_neg]; · simp
    intro h; exact hne (ps.uniq b hb e' he' h).symm
  · intro h; exact absurd he' h

lemma pivF_support (ps : PivotSys H F S) (x : Sym2 V → ℤ) {e' : Sym2 V}
    (he' : pivF ps x e' ≠ 0) : x e' ≠ 0 ∨ ∃ e ∈ S, x e ≠ 0 ∧ e' ∈ triEdges (ps.piv e) := by
  by_contra h
  push_neg at h
  apply he'
  rw [pivF, Pi.sub_apply, triBd_pivC, Finset.sum_apply, h.1, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun e he => ?_
  simp only [Pi.smul_apply, smul_eq_mul, ind]
  by_cases hx : x e = 0
  · simp [hx]
  · rw [if_neg (h.2 e he hx)]; simp

lemma l1E_pivF_le (ps : PivotSys H F S) (x : Sym2 V → ℤ) : l1E (pivF ps x) ≤ 4 * l1E x := by
  have := l1E_sub_le x (triBd H F (pivC ps x))
  have := l1E_triBd_le H F (pivC ps x)
  have := sum_abs_pivC_le ps x
  unfold pivF; linarith

lemma pivF_mem (ps : PivotSys H F S) {x : Sym2 V → ℤ} (hx : x ∈ localGroup H F) :
    pivF ps x ∈ localGroup H F :=
  Submodule.sub_mem _ hx (triBd_mem_localGroup H F _)

/-- `pivF` como homomorfismo. -/
def pivL (ps : PivotSys H F S) : (Sym2 V → ℤ) →ₗ[ℤ] (Sym2 V → ℤ) :=
  LinearMap.id - (triBd H F).comp (pivC ps)

lemma pivL_apply (ps : PivotSys H F S) (x : Sym2 V → ℤ) : pivL ps x = pivF ps x := rfl

/-! ## Evento de estrellas -/

omit [Fintype V] in
lemma diamLe_bot (D : ℕ) : DiamLe (⊥ : SimpleGraph V) D := by
  intro u v huv
  have : u = v := by
    obtain ⟨p⟩ := huv
    cases p with
    | nil => rfl
    | cons h _ => exact absurd h (by simp)
  subst this
  exact ⟨SimpleGraph.Walk.nil, by simp⟩

lemma triBd_eq_of_support_triAt {c : Finset V → ℤ} {v : V}
    (hc : ∀ T, c T ≠ 0 → T ∈ triAt H F v) :
    triBd H F c = ∑ T ∈ triAt H F v, c T • ind (triEdges T) := by
  change ∑ T ∈ allowed H F, c T • ind (triEdges T) = _
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) fun T _ hT => ?_
  have : c T = 0 := by by_contra h; exact hT (hc T h)
  simp [this]

/-- **Evento de estrellas.** -/
theorem star_event {M : Submodule ℤ (Sym2 V → ℤ)} (R : Finset V)
    (G : V → SimpleGraph V) (hG : ∀ v ∈ R, G v ≤ linkGraph H F v)
    (hbase : ∀ v ∈ R, ∀ a b, (G v).Adj a b → a ∉ R) {D : ℕ}
    (hD : ∀ v ∈ R, DiamLe (G v) D)
    (hin : ∀ x ∈ M, ∀ v ∈ R, starProj v x ∈ incLattice (G v)) :
    ∃ c : M →ₗ[ℤ] (Finset V → ℤ), ∀ x : M,
      (∀ T, c x T ≠ 0 → ∃ v ∈ R, ∃ a b, (G v).Adj a b ∧ T = {v, a, b}) ∧
      (∀ v ∈ R, starProj v (x.1 - triBd H F (c x)) = 0) ∧
      ∑ T, |c x T| ≤ (2 * D + 1) * (2 * l1E x.1) := by
  -- proyecciones lineales
  let y : ∀ v : R, M →ₗ[ℤ] incLattice (G v) := fun v =>
    LinearMap.codRestrict _ ((starProj v.1).comp M.subtype) (fun x => hin x.1 x.2 v.1 v.2)
  let cv : ∀ v : R, M →ₗ[ℤ] (Finset V → ℤ) := fun v =>
    (edgeTriL H F v.1).comp ((secL (hD v.1 v.2)).comp (y v))
  have hsupp_sec : ∀ (v : R) (x : M) e, secL (hD v.1 v.2) (y v x) e ≠ 0 →
      e ∈ (G v.1).edgeSet := fun v x e he => secL_support _ _ e he
  have hsupp_link : ∀ (v : R) (x : M) e, secL (hD v.1 v.2) (y v x) e ≠ 0 →
      e ∈ (linkGraph H F v.1).edgeSet := fun v x e he =>
    SimpleGraph.edgeSet_mono (hG v.1 v.2) (hsupp_sec v x e he)
  -- soporte de cada `cv`
  have hcv_supp : ∀ (v : R) (x : M) T, cv v x T ≠ 0 →
      ∃ a b, (G v.1).Adj a b ∧ T = {v.1, a, b} := by
    intro v x T hT
    change edgeTriL H F v.1 (secL (hD v.1 v.2) (y v x)) T ≠ 0 at hT
    rw [edgeTriL_apply] at hT
    obtain ⟨e, he, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
    obtain ⟨-, hTe⟩ := Finset.mem_filter.1 he
    have hGe := hsupp_sec v x e hne
    induction e using Sym2.ind with
    | _ a b => exact ⟨a, b, hGe, by rw [← hTe, triOf_mk]⟩
  have hcv_triAt : ∀ (v : R) (x : M) T, cv v x T ≠ 0 → T ∈ triAt H F v.1 := by
    intro v x T hT
    exact edgeTriL_support H F v.1 _ hT
  refine ⟨∑ v : R, cv v, fun x => ⟨?_, ?_, ?_⟩⟩
  · intro T hT
    rw [LinearMap.sum_apply, Finset.sum_apply] at hT
    obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
    obtain ⟨a, b, hab, rfl⟩ := hcv_supp v x T hv
    exact ⟨v.1, v.2, a, b, hab, rfl⟩
  · intro v hv
    rw [map_sub, LinearMap.sum_apply, map_sum, map_sum]
    have hself : starProj v (triBd H F (cv ⟨v, hv⟩ x)) = starProj v x.1 := by
      rw [triBd_eq_of_support_triAt (hcv_triAt ⟨v, hv⟩ x), ← starComb_eq_starProj]
      change starComb H F v (edgeTriL H F v (secL (hD v hv) (y ⟨v, hv⟩ x))) = _
      rw [starComb_edgeTriL H F v _ (hsupp_link ⟨v, hv⟩ x), bd_secL]
      rfl
    have hother : ∀ v' : R, v' ≠ ⟨v, hv⟩ → starProj v (triBd H F (cv v' x)) = 0 := by
      intro v' hne
      rw [triBd_eq_of_support_triAt (hcv_triAt v' x), map_sum]
      refine Finset.sum_eq_zero fun T _ => ?_
      by_cases hT : cv v' x T = 0
      · simp [hT]
      obtain ⟨a, b, hab, rfl⟩ := hcv_supp v' x T hT
      rw [map_zsmul, starProj_ind_tri_of_not_mem, smul_zero]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => hne (Subtype.ext h.symm), fun h => hbase v'.1 v'.2 a b hab (h ▸ hv),
        fun h => hbase v'.1 v'.2 b a hab.symm (h ▸ hv)⟩
    rw [Finset.sum_eq_single ⟨v, hv⟩ (fun v' _ hne => hother v' hne) (by simp), hself,
      sub_self]
  · rw [LinearMap.sum_apply]
    calc ∑ T, |(∑ v : R, cv v x) T|
        ≤ ∑ T, ∑ v : R, |cv v x T| := Finset.sum_le_sum fun T _ => by
          rw [Finset.sum_apply]; exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ v : R, ∑ T, |cv v x T| := Finset.sum_comm
      _ = ∑ v : R, ∑ T ∈ triAt H F v.1, |cv v x T| := Finset.sum_congr rfl fun v _ => by
          symm
          refine Finset.sum_subset (Finset.subset_univ _) fun T _ hT => ?_
          have : cv v x T = 0 := by by_contra h; exact hT (hcv_triAt v x T h)
          simp [this]
      _ ≤ ∑ v : R, (2 * D + 1) * l1V (starProj v.1 x.1) := Finset.sum_le_sum fun v _ =>
          (sum_abs_edgeTriL_le H F v.1 _).trans (l1E_secL_le (hD v.1 v.2) (y v x))
      _ = (2 * D + 1) * ∑ v ∈ R, l1V (starProj v x.1) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_coe_sort R (fun v => l1V (starProj v x.1))
      _ ≤ (2 * D + 1) * (2 * l1E x.1) :=
          mul_le_mul_of_nonneg_left (sum_l1V_starProj_le R x.1) (by positivity)

end TypedTriangle
