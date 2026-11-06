/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Corners.Defs
public import CDRBicolour.Absorption.BRIFinal

/-!
# A bounded right inverse for the majority-type host (item 3, corners)

A minority triangle `T = {u, u', w}` (`u, u' ∈ X`, `w ∈ X+2`) is replaced by `ψ(T) = φ(u,u',w) +
φ(u',u,w)`, where

`φ(p,q,r) = Σ_{z ∈ X+1} (1/(2|X+1|))·[pqz] + κ_X Σ_{x ∈ X∖p} Σ_{w₁ ≠ w₂ ∈ X+2 ∖ r} G(r,p,x,w₁,w₂)`,

`G(r,p,x,w₁,w₂) = [rw₁p] + [rw₂p] − [w₁w₂p] − [rw₁x] − [rw₂x] + [w₁w₂x]` has incidence
`2(𝟏_{rp} − 𝟏_{rx})`, and `κ_X = 1/(2|X|(|X+2|−1)(|X+2|−2))`.  All these triangles are majority
triangles, and the incidence of `ψ(T)` is `𝟏_T + Σ_v π_v(T)·ρ_v`, with
`ρ_v = (1/|X_v+1|) Σ_{z ∈ X_v+1} 𝟏_{vz}` (`Minc_psiT`).  Hence the operator `Ψ₃` (identity on
majority triangles, `ψ` on minority ones) satisfies `M₃ Ψ₃ c = M c + Σ_v π_v(M c)·ρ_v`
(`Minc_Psi3`), which is `M c` on `ker π`.  Composed with the CDR bounded inverse (`ker π ⊆ ker ℓ`)
it is a bounded right inverse of the majority incidence on `ker π` (`bri3`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Corners

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Refined

variable {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin 3)

/-! ### Definitions -/

/-- A class. -/
def cls (k : Fin 3) : Finset V := univ.filter fun v => lab v = k

omit [DecidableEq V] in
theorem mem_cls {k : Fin 3} {v : V} : v ∈ cls lab k ↔ lab v = k := by simp [cls]

omit [DecidableEq V] in
theorem card_cls (k : Fin 3) : #(cls lab k) = csz lab k := rfl

/-- The indicator of one triangle. -/
def dl (S T' : Finset V) : ℝ := if T' = S then 1 else 0

/-- The gadget `G(r,p,x,w₁,w₂)`. -/
def gadG (r p x w₁ w₂ : V) : Finset V → ℝ :=
  dl {r, w₁, p} + dl {r, w₂, p} - dl {w₁, w₂, p} - dl {r, w₁, x} - dl {r, w₂, x} + dl {w₁, w₂, x}

/-- An ordered minority triangle `(p, q, r)`: `p ≠ q` in one class, `r` two classes later. -/
def okM (p q r : V) : Prop := p ≠ q ∧ lab q = lab p ∧ lab r = lab p + 2

instance (p q r : V) : Decidable (okM lab p q r) := by unfold okM; infer_instance

/-- `κ_X`. -/
def kap (X : Fin 3) : ℝ :=
  1 / (2 * (csz lab X : ℝ) * (((csz lab (X + 2) - 1 : ℕ) : ℝ) * ((csz lab (X + 2) - 2 : ℕ) : ℝ)))

/-- `φ(p,q,r)`. -/
def phi (p q r : V) : Finset V → ℝ :=
  (∑ z ∈ cls lab (lab p + 1), (1 / (2 * (csz lab (lab p + 1) : ℝ))) • dl {p, q, z}) +
    ∑ x ∈ (cls lab (lab p)).erase p, ∑ w₁ ∈ (cls lab (lab r)).erase r,
      ∑ w₂ ∈ ((cls lab (lab r)).erase r).erase w₁, kap lab (lab p) • gadG r p x w₁ w₂

/-- Minority triangles of the complete host. -/
def minS : Finset (Finset V) := (triG lab cdrF).filter fun T => T ∉ triG lab majF

/-- `ψ(T)`: the sum of `φ` over the ordered minority representations of `T`. -/
def psiT (T : Finset V) : Finset V → ℝ :=
  ∑ p ∈ T, ∑ q ∈ T, ∑ r ∈ T, if okM lab p q r then phi lab p q r else 0

/-- The replacement operator. -/
def Psi3 : (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun c T' := (if T' ∈ triG lab majF then c T' else 0) + ∑ T ∈ minS lab, c T * psiT lab T T'
  map_add' c c' := by
    funext T'
    simp only [Pi.add_apply, add_mul, sum_add_distrib]
    split_ifs <;> ring
  map_smul' r c := by
    funext T'
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, mul_sum, mul_assoc]
    split_ifs <;> ring

/-- `ρ_v`. -/
def rv (v : V) : E0 V → ℝ := fun e =>
  (1 / (csz lab (lab v + 1) : ℝ)) * ∑ z ∈ cls lab (lab v + 1), if e.1 = s(v, z) then 1 else 0

/-! ### Elementary facts -/

theorem fin3_add2_add1 (x : Fin 3) : x + 2 + 1 = x := by revert x; decide
theorem fin3_ne_add1 (x : Fin 3) : x + 1 ≠ x := by revert x; decide
theorem fin3_add2_ne (x : Fin 3) : x + 2 ≠ x := by revert x; decide
theorem fin3_add1_ne_add2 (x : Fin 3) : x + 1 ≠ x + 2 := by revert x; decide

omit [Fintype V] in
theorem sym2_three {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    s(a, b) ≠ s(a, c) ∧ s(a, b) ≠ s(b, c) ∧ s(a, c) ≠ s(b, c) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hbc h
    · exact hac h
  · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hab h
    · exact hac h
  · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hab h
    · exact hac h

/-- Membership in the edge set of a triangle, as a sum of three indicators. -/
theorem ind_tri {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (e : Sym2 V) :
    (if e ∈ triEdges ({a, b, c} : Finset V) then (1 : ℝ) else 0) =
      (if e = s(a, b) then 1 else 0) + (if e = s(a, c) then 1 else 0) +
        (if e = s(b, c) then 1 else 0) := by
  rw [triEdges_triple hab hac hbc]
  obtain ⟨h1, h2, h3⟩ := sym2_three hab hac hbc
  by_cases e1 : e = s(a, b)
  · subst e1; simp [h1, h2]
  by_cases e2 : e = s(a, c)
  · subst e2; simp [h3, e1]
  by_cases e3 : e = s(b, c)
  · subst e3; simp [e1, e2]
  simp [e1, e2, e3]

/-- A majority triangle from its labels. -/
theorem tri_maj {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hb : lab b = lab a)
    (hc : lab c = lab a + 1) : ({a, b, c} : Finset V) ∈ triG lab majF := by
  rw [gmem_tri]
  refine ⟨card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩, fun x _ y _ hxy => hxy, ?_⟩
  show ({a, b, c} : Finset V).val.map lab ∈ majF
  rw [val_map_triple lab hab hac.symm hbc.symm, hb, hc]
  exact ⟨lab a, rfl⟩

theorem Minc_dl (S : Finset V) (e : E0 V) :
    MincG lab majF (dl S) e = if S ∈ triG lab majF ∧ e.1 ∈ triEdges S then 1 else 0 := by
  simp only [MincG, LinearMap.coe_mk, AddHom.coe_mk, dl]
  rw [sum_ite_eq']
  simp only [mem_filter]

theorem Minc_dl_of {S : Finset V} (hS : S ∈ triG lab majF) (e : E0 V) :
    MincG lab majF (dl S) e = if e.1 ∈ triEdges S then 1 else 0 := by
  rw [Minc_dl]; simp only [hS, true_and]

/-! ### The incidence of the gadget -/

theorem Minc_gad {r p x w₁ w₂ : V} {X : Fin 3} (hr : lab r = X + 2) (h1 : lab w₁ = X + 2)
    (h2 : lab w₂ = X + 2) (hp : lab p = X) (hx : lab x = X) (hr1 : r ≠ w₁) (hr2 : r ≠ w₂)
    (h12 : w₁ ≠ w₂) (_hpx : p ≠ x) (e : E0 V) :
    MincG lab majF (gadG r p x w₁ w₂) e =
      2 * (if e.1 = s(r, p) then 1 else 0) - 2 * (if e.1 = s(r, x) then 1 else 0) := by
  have nW : ∀ {a b : V}, lab a = X + 2 → lab b = X → a ≠ b := fun ha hb h => by
    rw [h, hb] at ha; exact fin3_add2_ne X ha.symm
  have rp := nW hr hp; have rx := nW hr hx; have w1p := nW h1 hp; have w1x := nW h1 hx
  have w2p := nW h2 hp; have w2x := nW h2 hx
  have lw : ∀ {a : V}, lab a = X → lab a = (X + 2) + 1 := fun ha => by rw [ha, fin3_add2_add1]
  have T1 := tri_maj lab hr1 rp w1p (by rw [h1, hr]) (by rw [hr]; exact lw hp)
  have T2 := tri_maj lab hr2 rp w2p (by rw [h2, hr]) (by rw [hr]; exact lw hp)
  have T3 := tri_maj lab h12 w1p w2p (by rw [h2, h1]) (by rw [h1]; exact lw hp)
  have T4 := tri_maj lab hr1 rx w1x (by rw [h1, hr]) (by rw [hr]; exact lw hx)
  have T5 := tri_maj lab hr2 rx w2x (by rw [h2, hr]) (by rw [hr]; exact lw hx)
  have T6 := tri_maj lab h12 w1x w2x (by rw [h2, h1]) (by rw [h1]; exact lw hx)
  unfold gadG
  simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply, Minc_dl, T1, T2, T3, T4, T5, T6,
    true_and]
  rw [ind_tri hr1 rp w1p, ind_tri hr2 rp w2p, ind_tri h12 w1p w2p, ind_tri hr1 rx w1x,
    ind_tri hr2 rx w2x, ind_tri h12 w1x w2x]
  ring

/-! ### The incidence of `φ` and of `ψ` -/

theorem sum_erase_erase_const {s : Finset V} {r : V} (hr : r ∈ s) (f : ℝ) :
    ∑ w₁ ∈ s.erase r, ∑ _w₂ ∈ (s.erase r).erase w₁, f =
      (((#s - 1 : ℕ) : ℝ) * ((#s - 2 : ℕ) : ℝ)) * f := by
  have : ∀ w₁ ∈ s.erase r, ∑ _w₂ ∈ (s.erase r).erase w₁, f = ((#s - 2 : ℕ) : ℝ) * f := by
    intro w₁ hw₁
    rw [sum_const, nsmul_eq_mul, card_erase_of_mem hw₁, card_erase_of_mem hr]
    congr 2
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul, card_erase_of_mem hr]
  ring

/-- **Incidence of `φ`.** -/
theorem Minc_phi (hcls : ∀ k, 3 ≤ csz lab k) {p q r : V} (h : okM lab p q r) (e : E0 V) :
    MincG lab majF (phi lab p q r) e =
      (1 / 2) * (if e.1 = s(p, q) then 1 else 0) + (1 / 2) * (rv lab p e + rv lab q e) +
        (if e.1 = s(r, p) then 1 else 0) - rv lab r e := by
  obtain ⟨hpq, hq, hr⟩ := h
  set X := lab p with hX
  have hsX : (0 : ℝ) < csz lab X := by exact_mod_cast (show 0 < csz lab X by have := hcls X; omega)
  have hsX1 : (0 : ℝ) < csz lab (X + 1) := by
    exact_mod_cast (show 0 < csz lab (X + 1) by have := hcls (X + 1); omega)
  have hW1 : (0 : ℝ) < ((csz lab (X + 2) - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < csz lab (X + 2) - 1 by have := hcls (X + 2); omega)
  have hW2 : (0 : ℝ) < ((csz lab (X + 2) - 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < csz lab (X + 2) - 2 by have := hcls (X + 2); omega)
  set I : V → V → ℝ := fun a b => if e.1 = s(a, b) then 1 else 0 with hI
  unfold phi
  rw [map_add, Pi.add_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_sum, Finset.sum_apply]
  -- the `X`-part
  have hA : ∀ z ∈ cls lab (X + 1), (1 / (2 * (csz lab (X + 1) : ℝ))) *
      MincG lab majF (dl {p, q, z}) e =
        (1 / (2 * (csz lab (X + 1) : ℝ))) * (I p q + I p z + I q z) := by
    intro z hz
    rw [mem_cls] at hz
    have hpz : p ≠ z := fun h' => fin3_ne_add1 X (by rw [← hz, ← h'])
    have hqz : q ≠ z := fun h' => fin3_ne_add1 X (by rw [← hz, ← h', hq])
    rw [Minc_dl_of lab (tri_maj lab hpq hpz hqz hq hz), ind_tri hpq hpz hqz]
  rw [sum_congr rfl hA, ← mul_sum, sum_add_distrib, sum_add_distrib, sum_const, card_cls,
    nsmul_eq_mul]
  -- the `W`-part
  have hrW : r ∈ cls lab (lab r) := (mem_cls lab).2 rfl
  have hB : ∀ x ∈ (cls lab X).erase p, ∑ w₁ ∈ (cls lab (lab r)).erase r,
      ∑ w₂ ∈ ((cls lab (lab r)).erase r).erase w₁, kap lab X *
        MincG lab majF (gadG r p x w₁ w₂) e =
      (((csz lab (X + 2) - 1 : ℕ) : ℝ) * ((csz lab (X + 2) - 2 : ℕ) : ℝ)) *
        (kap lab X * (2 * I r p - 2 * I r x)) := by
    intro x hx
    obtain ⟨hxp, hx⟩ := mem_erase.1 hx
    rw [mem_cls] at hx
    have hin : ∀ w₁ ∈ (cls lab (lab r)).erase r, ∀ w₂ ∈ ((cls lab (lab r)).erase r).erase w₁,
        kap lab X * MincG lab majF (gadG r p x w₁ w₂) e = kap lab X * (2 * I r p - 2 * I r x) := by
      intro w₁ hw₁ w₂ hw₂
      obtain ⟨h21, hw₂⟩ := mem_erase.1 hw₂
      obtain ⟨h2r, hw₂⟩ := mem_erase.1 hw₂
      obtain ⟨h1r, hw₁⟩ := mem_erase.1 hw₁
      rw [mem_cls] at hw₁ hw₂
      rw [Minc_gad lab hr (hw₁.trans hr) (hw₂.trans hr) rfl hx (Ne.symm h1r) (Ne.symm h2r)
        (Ne.symm h21) (Ne.symm hxp)]
    rw [sum_congr rfl fun w₁ hw₁ => sum_congr rfl (hin w₁ hw₁), sum_erase_erase_const hrW,
      card_cls, hr]
  rw [sum_congr rfl hB, ← mul_sum, ← mul_sum]
  have hpX : p ∈ cls lab X := (mem_cls lab).2 rfl
  rw [sum_erase (f := fun x => 2 * I r p - 2 * I r x) _ (by simp)]
  rw [sum_sub_distrib, sum_const, card_cls, nsmul_eq_mul, ← mul_sum]
  -- the vectors `ρ`
  have e1 : rv lab p e = (1 / (csz lab (X + 1) : ℝ)) * ∑ z ∈ cls lab (X + 1), I p z := rfl
  have e2 : rv lab q e = (1 / (csz lab (X + 1) : ℝ)) * ∑ z ∈ cls lab (X + 1), I q z := by
    simp only [rv, hq]; rfl
  have e3 : rv lab r e = (1 / (csz lab X : ℝ)) * ∑ x ∈ cls lab X, I r x := by
    simp only [rv, hr, fin3_add2_add1]; rfl
  rw [e1, e2, e3]
  unfold kap
  field_simp
  ring

/-- `ψ` of a minority triangle: its two ordered representations. -/
theorem psiT_eq {u u' w : V} (huu' : u ≠ u') (hl1 : lab u' = lab u) (hl2 : lab w = lab u + 2) :
    psiT lab {u, u', w} = phi lab u u' w + phi lab u' u w := by
  have huw : u ≠ w := fun h => fin3_add2_ne (lab u) (by rw [← hl2, h])
  have hu'w : u' ≠ w := fun h => fin3_add2_ne (lab u) (by rw [← hl2, ← h, hl1])
  have n1 : lab u ≠ lab u + 2 := (fin3_add2_ne _).symm
  have n2 : lab u + 2 ≠ lab u + 2 + 2 := by generalize lab u = x; revert x; decide
  have n3 : lab u ≠ lab u + 2 + 2 := by generalize lab u = x; revert x; decide
  have hn1 : u ∉ ({u', w} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨huu', huw⟩
  have hn2 : u' ∉ ({w} : Finset V) := by simp only [mem_singleton]; exact hu'w
  simp only [psiT, sum_insert hn1, sum_insert hn2, sum_singleton, okM, hl1, hl2, ne_eq,
    not_true_eq_false, false_and, if_false, huu', Ne.symm huu', huw, hu'w, Ne.symm huw,
    Ne.symm hu'w, not_false_eq_true, true_and, n1, n2, n3, n1.symm, n2.symm, n3.symm, if_true,
    and_true, and_false, add_zero, zero_add]

/-- **Incidence of `ψ(T)`**: `𝟏_T + Σ_v π_v(T) ρ_v`. -/
theorem Minc_psiT (hcls : ∀ k, 3 ≤ csz lab k) {T : Finset V} (hT : T ∈ minS lab) (e : E0 V) :
    MincG lab majF (psiT lab T) e =
      (if e.1 ∈ triEdges T then 1 else 0) + ∑ v, piT lab T v * rv lab v e := by
  obtain ⟨hTc, hTm⟩ := mem_filter.1 hT
  obtain ⟨X, hX⟩ := (cdr_split lab hTc).resolve_left hTm
  obtain ⟨u, u', w, rfl, huu', hu, hu', hw⟩ := min_shape lab hTc hX
  have hl1 : lab u' = lab u := hu'.trans hu.symm
  have hl2 : lab w = lab u + 2 := by rw [hw, hu]
  have huw : u ≠ w := fun h => fin3_add2_ne (lab u) (by rw [← hl2, h])
  have hu'w : u' ≠ w := fun h => fin3_add2_ne (lab u) (by rw [← hl2, ← h, hl1])
  rw [psiT_eq lab huu' hl1 hl2, map_add, Pi.add_apply,
    Minc_phi lab hcls ⟨huu', hl1, hl2⟩, Minc_phi lab hcls ⟨Ne.symm huu', hl1.symm, by rw [hl1, hl2]⟩,
    ind_tri huu' huw hu'w]
  have hsum : ∑ v, piT lab {u, u', w} v * rv lab v e = rv lab u e + rv lab u' e - 2 * rv lab w e := by
    simp only [min_piT lab huu' hl1 hl2]
    simp only [add_mul, sub_mul, mul_assoc, sum_add_distrib, sum_sub_distrib, ← mul_sum, ite_mul,
      one_mul, zero_mul, sum_ite_eq', mem_univ, if_true]
  rw [hsum, show s(w, u) = s(u, w) from Sym2.eq_swap, show s(w, u') = s(u', w) from Sym2.eq_swap,
    show s(u', u) = s(u, u') from Sym2.eq_swap]
  ring

theorem triG_maj_sub {T : Finset V} (hT : T ∈ triG lab majF) : T ∈ triG lab cdrF := by
  rw [gmem_tri] at hT ⊢
  exact ⟨hT.1, hT.2.1, majF_sub hT.2.2⟩

/-- `π_v(M c)` only sees the minority triangles. -/
theorem ell_wpi_minS (c : Finset V → ℝ) (v : V) :
    ellG' (wpi lab v) (MincG lab cdrF c) = ∑ T ∈ minS lab, c T * piT lab T v := by
  rw [ell_wpi_Minc]
  rw [show triG lab cdrF = (triG lab cdrF).filter (fun T => T ∈ triG lab majF) ∪ minS lab by
    ext T; simp only [mem_union, mem_filter, minS]; tauto]
  rw [sum_union (by
    rw [disjoint_left]; intro T h1 h2; exact (mem_filter.1 h2).2 (mem_filter.1 h1).2)]
  rw [sum_eq_zero fun T hT => by rw [maj_piT lab (mem_filter.1 hT).2, mul_zero], zero_add]

/-- **Incidence of `Ψ₃ c`.** -/
theorem Minc_Psi3 (hcls : ∀ k, 3 ≤ csz lab k) (c : Finset V → ℝ) :
    MincG lab majF (Psi3 lab c) =
      MincG lab cdrF c + ∑ v, ellG' (wpi lab v) (MincG lab cdrF c) • rv lab v := by
  funext e
  rw [Pi.add_apply, Finset.sum_apply]
  simp only [ell_wpi_minS, Pi.smul_apply, smul_eq_mul]
  have hL : MincG lab majF (Psi3 lab c) e =
      ∑ T' ∈ (triG lab majF).filter (fun T' => e.1 ∈ triEdges T'), c T' +
        ∑ T ∈ minS lab, c T * MincG lab majF (psiT lab T) e := by
    simp only [MincG, Psi3, LinearMap.coe_mk, AddHom.coe_mk]
    rw [sum_add_distrib]
    have hF : ∀ T' ∈ (triG lab majF).filter (fun T' => e.1 ∈ triEdges T'),
        (if T' ∈ triG lab majF then c T' else 0) = c T' := fun T' h => if_pos (mem_filter.1 h).1
    rw [sum_congr rfl hF, sum_comm]
    simp only [mul_sum]
  have hR : MincG lab cdrF c e =
      ∑ T' ∈ (triG lab majF).filter (fun T' => e.1 ∈ triEdges T'), c T' +
        ∑ T ∈ minS lab, c T * (if e.1 ∈ triEdges T then 1 else 0) := by
    simp only [MincG, LinearMap.coe_mk, AddHom.coe_mk]
    have hsplit : (triG lab cdrF).filter (fun T => e.1 ∈ triEdges T) =
        (triG lab majF).filter (fun T => e.1 ∈ triEdges T) ∪
          (minS lab).filter (fun T => e.1 ∈ triEdges T) := by
      ext T
      simp only [mem_filter, mem_union, minS]
      constructor
      · rintro ⟨hT, he⟩
        by_cases hm : T ∈ triG lab majF
        · exact Or.inl ⟨hm, he⟩
        · exact Or.inr ⟨⟨hT, hm⟩, he⟩
      · rintro (⟨hT, he⟩ | ⟨⟨hT, -⟩, he⟩)
        · exact ⟨triG_maj_sub lab hT, he⟩
        · exact ⟨hT, he⟩
    rw [hsplit, sum_union (by
      rw [disjoint_left]; intro T h1 h2
      exact (mem_filter.1 (mem_filter.1 h2).1).2 (mem_filter.1 h1).1)]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
  have h3 : ∑ T ∈ minS lab, c T * MincG lab majF (psiT lab T) e = ∑ T ∈ minS lab,
      c T * ((if e.1 ∈ triEdges T then 1 else 0) + ∑ v, piT lab T v * rv lab v e) :=
    sum_congr rfl fun T hT => by rw [Minc_psiT lab hcls hT e]
  rw [hL, hR, h3]
  simp only [mul_add, sum_add_distrib, mul_sum]
  rw [add_assoc]
  congr 2
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [sum_mul]
  exact sum_congr rfl fun T _ => by ring

/-! ### Counting placements -/

/-- Placements of `Fin k` with three prescribed values. -/
theorem card_fix3_le_gen {k : ℕ} {p q r : V} (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) :
    #(univ.filter fun t : Fin k → V => t i = p ∧ t j = q ∧ t l = r) ≤
      Fintype.card V ^ (k - 3) := by
  set S : Finset (Fin k) := {i, j, l}
  have hS : S.card = 3 := by
    rw [card_insert_of_notMem (by simp [hij, hil]), card_pair hjl]
  have hcard : Fintype.card {x // x ∉ S} = k - 3 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hS]
  calc #(univ.filter fun t : Fin k → V => t i = p ∧ t j = q ∧ t l = r)
      ≤ Fintype.card ({x // x ∉ S} → V) := by
        refine card_le_card_of_injOn (fun t x => t x.1) (fun _ _ => mem_univ _) ?_
        intro t ht t' ht' h
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht ht'
        funext x
        by_cases hx : x ∈ S
        · simp only [S, mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · rw [ht.1, ht'.1]
          · rw [ht.2.1, ht'.2.1]
          · rw [ht.2.2, ht'.2.2]
        · exact congrFun h ⟨x, hx⟩
    _ = Fintype.card V ^ (k - 3) := by rw [Fintype.card_fun, hcard]

/-- **At most `k³ nᵏ⁻³` placements of `Fin k` cover a given triangle.** -/
theorem card_cover_le_gen (k : ℕ) {T' : Finset V} (h3 : T'.card = 3) :
    #(univ.filter fun t : Fin k → V => T' ⊆ univ.image t) ≤ k ^ 3 * Fintype.card V ^ (k - 3) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp h3
  have hsub : (univ.filter fun t : Fin k → V => ({p, q, r} : Finset V) ⊆ univ.image t) ⊆
      (univ : Finset (Fin k × Fin k × Fin k)).biUnion fun ijl =>
        univ.filter fun t : Fin k → V => t ijl.1 = p ∧ t ijl.2.1 = q ∧ t ijl.2.2 = r := by
    intro t ht
    simp only [mem_filter, mem_univ, true_and, insert_subset_iff, singleton_subset_iff,
      mem_image] at ht
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨l, hl⟩⟩ := ht
    exact mem_biUnion.mpr ⟨(i, j, l), mem_univ _, by simp [hi, hj, hl]⟩
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  calc ∑ ijl : Fin k × Fin k × Fin k,
        #(univ.filter fun t : Fin k → V => t ijl.1 = p ∧ t ijl.2.1 = q ∧ t ijl.2.2 = r)
      ≤ ∑ _ijl : Fin k × Fin k × Fin k, Fintype.card V ^ (k - 3) := by
        refine sum_le_sum fun ijl _ => ?_
        obtain ⟨i, j, l⟩ := ijl
        by_cases hij : i = j
        · subst hij
          rw [card_eq_zero.mpr]; · exact Nat.zero_le _
          ext t; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          rintro ⟨h1, h2, -⟩; exact hpq (h1 ▸ h2)
        by_cases hil : i = l
        · subst hil
          rw [card_eq_zero.mpr]; · exact Nat.zero_le _
          ext t; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          rintro ⟨h1, -, h3⟩; exact hpr (h1 ▸ h3)
        by_cases hjl : j = l
        · subst hjl
          rw [card_eq_zero.mpr]; · exact Nat.zero_le _
          ext t; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          rintro ⟨-, h2, h3⟩; exact hqr (h2 ▸ h3)
        exact card_fix3_le_gen i j l hij hil hjl
    _ = k ^ 3 * Fintype.card V ^ (k - 3) := by simp; left; ring

omit [DecidableEq V] in
/-- Five nested sums are a sum over `Fin 5 → V`. -/
theorem sum_five (f : (Fin 5 → V) → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ g, f ![a, b, c, d, g] = ∑ t, f t := by
  let E : V × V × V × V × V ≃ (Fin 5 → V) :=
    { toFun := fun x => ![x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2]
      invFun := fun t => (t 0, t 1, t 2, t 3, t 4)
      left_inv := fun x => rfl
      right_inv := fun t => by funext i; fin_cases i <;> rfl }
  rw [← E.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

/-- The covering indicator of a placement of `Fin 5`. -/
def cov5 (T' : Finset V) (t : Fin 5 → V) : ℝ :=
  if T'.card = 3 ∧ T' ⊆ univ.image t then 1 else 0

theorem sum_cov5_le (T' : Finset V) :
    ∑ t : Fin 5 → V, cov5 T' t ≤ 125 * (Fintype.card V : ℝ) ^ 2 := by
  unfold cov5
  by_cases h3 : T'.card = 3
  · simp only [h3, true_and]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have := card_cover_le_gen 5 h3 (V := V)
    exact_mod_cast this
  · simp only [h3, false_and, if_false, sum_const_zero]
    positivity

omit [Fintype V] in
theorem cov5_nonneg (T' : Finset V) (t : Fin 5 → V) : 0 ≤ cov5 T' t := by
  unfold cov5; split_ifs <;> norm_num

/-- `|[T' = S]| ≤ cov5` when `S` is a triangle covered by the placement. -/
theorem dl_le_cov5 {S T' : Finset V} {t : Fin 5 → V} (hS : S.card = 3) (hSt : S ⊆ univ.image t) :
    |dl S T'| ≤ cov5 T' t := by
  unfold dl cov5
  by_cases h : T' = S
  · subst h; simp [hS, hSt]
  · rw [if_neg h, abs_zero]; split_ifs <;> norm_num

theorem abs_gad_le {r p x w₁ w₂ : V} (hrp : r ≠ p) (hrx : r ≠ x) (hr1 : r ≠ w₁) (hr2 : r ≠ w₂)
    (hpx : p ≠ x) (hp1 : p ≠ w₁) (hp2 : p ≠ w₂) (hx1 : x ≠ w₁) (hx2 : x ≠ w₂) (h12 : w₁ ≠ w₂)
    (T' : Finset V) :
    |gadG r p x w₁ w₂ T'| ≤ 6 * cov5 T' ![r, p, x, w₁, w₂] := by
  have im : ∀ a ∈ ({r, p, x, w₁, w₂} : Finset V), a ∈ univ.image ![r, p, x, w₁, w₂] := by
    intro a ha
    simp only [mem_insert, mem_singleton] at ha
    simp only [mem_image, mem_univ, true_and]
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  have sub : ∀ {a b c : V}, a ∈ ({r, p, x, w₁, w₂} : Finset V) →
      b ∈ ({r, p, x, w₁, w₂} : Finset V) → c ∈ ({r, p, x, w₁, w₂} : Finset V) →
        ({a, b, c} : Finset V) ⊆ univ.image ![r, p, x, w₁, w₂] := by
    intro a b c ha hb hc y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact im _ ha
    · exact im _ hb
    · exact im _ hc
  have c3 : ∀ {a b c : V}, a ≠ b → a ≠ c → b ≠ c → ({a, b, c} : Finset V).card = 3 :=
    fun h1 h2 h3 => card_eq_three.mpr ⟨_, _, _, h1, h2, h3, rfl⟩
  have m1 : r ∈ ({r, p, x, w₁, w₂} : Finset V) := by simp
  have m2 : p ∈ ({r, p, x, w₁, w₂} : Finset V) := by simp
  have m3 : x ∈ ({r, p, x, w₁, w₂} : Finset V) := by simp
  have m4 : w₁ ∈ ({r, p, x, w₁, w₂} : Finset V) := by simp
  have m5 : w₂ ∈ ({r, p, x, w₁, w₂} : Finset V) := by simp
  have b1 := dl_le_cov5 (T' := T') (c3 hr1 hrp (Ne.symm hp1)) (sub m1 m4 m2)
  have b2 := dl_le_cov5 (T' := T') (c3 hr2 hrp (Ne.symm hp2)) (sub m1 m5 m2)
  have b3 := dl_le_cov5 (T' := T') (c3 h12 (Ne.symm hp1) (Ne.symm hp2)) (sub m4 m5 m2)
  have b4 := dl_le_cov5 (T' := T') (c3 hr1 hrx (Ne.symm hx1)) (sub m1 m4 m3)
  have b5 := dl_le_cov5 (T' := T') (c3 hr2 hrx (Ne.symm hx2)) (sub m1 m5 m3)
  have b6 := dl_le_cov5 (T' := T') (c3 h12 (Ne.symm hx1) (Ne.symm hx2)) (sub m4 m5 m3)
  unfold gadG
  simp only [Pi.add_apply, Pi.sub_apply]
  have t1 := abs_add_le (dl {r, w₁, p} T' + dl {r, w₂, p} T' - dl {w₁, w₂, p} T' - dl {r, w₁, x} T' -
    dl {r, w₂, x} T') (dl {w₁, w₂, x} T')
  have t2 := abs_sub (dl {r, w₁, p} T' + dl {r, w₂, p} T' - dl {w₁, w₂, p} T' - dl {r, w₁, x} T')
    (dl {r, w₂, x} T')
  have t3 := abs_sub (dl {r, w₁, p} T' + dl {r, w₂, p} T' - dl {w₁, w₂, p} T') (dl {r, w₁, x} T')
  have t4 := abs_sub (dl {r, w₁, p} T' + dl {r, w₂, p} T') (dl {w₁, w₂, p} T')
  have t5 := abs_add_le (dl {r, w₁, p} T') (dl {r, w₂, p} T')
  linarith

/-! ### The bound -/

/-- `κ` for a lower bound `m` on the class sizes. -/
def kapM (m : ℕ) : ℝ := 1 / (2 * (m : ℝ) * (((m - 1 : ℕ) : ℝ) * ((m - 2 : ℕ) : ℝ)))

theorem kap_le {m : ℕ} (hm : ∀ k, m ≤ csz lab k) (h3 : 3 ≤ m) (X : Fin 3) :
    kap lab X ≤ kapM m := by
  unfold kap kapM
  have a1 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have a2 : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have a3 : (0 : ℝ) < ((m - 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 2 by omega)
  have b1 : (m : ℝ) ≤ csz lab X := by exact_mod_cast hm X
  have b2 : ((m - 1 : ℕ) : ℝ) ≤ ((csz lab (X + 2) - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show m - 1 ≤ csz lab (X + 2) - 1 by have := hm (X + 2); omega)
  have b3 : ((m - 2 : ℕ) : ℝ) ≤ ((csz lab (X + 2) - 2 : ℕ) : ℝ) := by
    exact_mod_cast (show m - 2 ≤ csz lab (X + 2) - 2 by have := hm (X + 2); omega)
  apply one_div_le_one_div_of_le (by positivity)
  have := mul_le_mul b2 b3 a3.le (a2.le.trans b2)
  have := mul_le_mul (mul_le_mul_of_nonneg_left b1 (by norm_num : (0 : ℝ) ≤ 2)) this
    (by positivity) (by positivity)
  linarith

/-- The covering indicator for the `X`-part. -/
def dX (T' : Finset V) (p q z : V) : ℝ :=
  (if T'.card ≤ 3 then 1 else 0) * ((if p ∈ T' then 1 else 0) * (if q ∈ T' then 1 else 0) *
    (if z ∈ T' then 1 else 0))

omit [Fintype V] in
theorem dX_nonneg (T' : Finset V) (p q z : V) : 0 ≤ dX T' p q z := by
  unfold dX; split_ifs <;> norm_num

omit [Fintype V] in
theorem abs_dl_le_dX (T' : Finset V) (p q z : V) : |dl {p, q, z} T'| ≤ dX T' p q z := by
  unfold dl
  by_cases h : T' = {p, q, z}
  · subst h
    have hc : ({p, q, z} : Finset V).card ≤ 3 := card_le_three
    simp [dX, hc]
  · rw [if_neg h, abs_zero]; exact dX_nonneg _ _ _ _

theorem sum_dX_le (T' : Finset V) : ∑ p, ∑ q, ∑ z, dX T' p q z ≤ 27 := by
  unfold dX
  simp only [← mul_sum, ← sum_mul, sum_boole, Nat.cast_id]
  rw [show (univ.filter fun x => x ∈ T') = T' by ext; simp]
  by_cases hc : T'.card ≤ 3
  · rw [if_pos hc, one_mul]
    have h : (#T' : ℝ) ≤ 3 := by exact_mod_cast hc
    have h0 : (0 : ℝ) ≤ #T' := by positivity
    nlinarith [mul_le_mul h h h0 (by norm_num : (0 : ℝ) ≤ 3)]
  · rw [if_neg hc, zero_mul]; norm_num

/-- **The bound on `φ`.** -/
theorem abs_phi_le {m : ℕ} (hm : ∀ k, m ≤ csz lab k) (h3 : 3 ≤ m) {p q r : V}
    (h : okM lab p q r) (T' : Finset V) :
    |phi lab p q r T'| ≤ (1 / (2 * (m : ℝ))) * ∑ z, dX T' p q z +
      6 * kapM m * ∑ x, ∑ w₁, ∑ w₂, cov5 T' ![r, p, x, w₁, w₂] := by
  obtain ⟨hpq, hq, hr⟩ := h
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hkap := kap_le lab hm h3 (lab p)
  have hkap0 : 0 ≤ kap lab (lab p) := by unfold kap; positivity
  unfold phi
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine (sum_le_sum fun z _ => ?_).trans (sum_le_sum_of_subset_of_nonneg (subset_univ _)
      fun z _ _ => mul_nonneg (by positivity) (dX_nonneg _ _ _ _))
    have hc0 : (0 : ℝ) < csz lab (lab p + 1) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < m) (hm _))
    rw [abs_mul, abs_of_pos (by positivity)]
    refine mul_le_mul ?_ (abs_dl_le_dX _ _ _ _) (abs_nonneg _) (by positivity)
    apply one_div_le_one_div_of_le (by positivity)
    have : (m : ℝ) ≤ csz lab (lab p + 1) := by exact_mod_cast hm _
    linarith
  · refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine (sum_le_sum fun x hx => ?_).trans (sum_le_sum_of_subset_of_nonneg (subset_univ _)
      fun x _ _ => mul_nonneg (by unfold kapM; positivity)
        (sum_nonneg fun _ _ => sum_nonneg fun _ _ => cov5_nonneg _ _))
    obtain ⟨hxp, hx⟩ := mem_erase.1 hx
    rw [mem_cls] at hx
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine (sum_le_sum fun w₁ hw₁ => ?_).trans (sum_le_sum_of_subset_of_nonneg (subset_univ _)
      fun w₁ _ _ => mul_nonneg (by unfold kapM; positivity)
        (sum_nonneg fun _ _ => cov5_nonneg _ _))
    obtain ⟨h1r, hw₁⟩ := mem_erase.1 hw₁
    rw [mem_cls] at hw₁
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine (sum_le_sum fun w₂ hw₂ => ?_).trans (sum_le_sum_of_subset_of_nonneg (subset_univ _)
      fun w₂ _ _ => mul_nonneg (by unfold kapM; positivity) (cov5_nonneg _ _))
    obtain ⟨h21, hw₂⟩ := mem_erase.1 hw₂
    obtain ⟨h2r, hw₂⟩ := mem_erase.1 hw₂
    rw [mem_cls] at hw₂
    have nW : ∀ {a b : V}, lab a = lab p + 2 → lab b = lab p → a ≠ b := fun ha hb h => by
      rw [h, hb] at ha; exact fin3_add2_ne _ ha.symm
    have l1 : lab w₁ = lab p + 2 := hw₁.trans hr
    have l2 : lab w₂ = lab p + 2 := hw₂.trans hr
    have hg := abs_gad_le (nW hr rfl) (nW hr hx) (Ne.symm h1r) (Ne.symm h2r) (Ne.symm hxp)
      (Ne.symm (nW l1 rfl)) (Ne.symm (nW l2 rfl)) (Ne.symm (nW l1 hx)) (Ne.symm (nW l2 hx))
      (Ne.symm h21) T'
    rw [abs_mul, abs_of_nonneg hkap0]
    calc kap lab (lab p) * |gadG r p x w₁ w₂ T'| ≤ kapM m * (6 * cov5 T' ![r, p, x, w₁, w₂]) :=
          mul_le_mul hkap hg (abs_nonneg _) (by unfold kapM; positivity)
      _ = 6 * kapM m * cov5 T' ![r, p, x, w₁, w₂] := by ring

omit [Fintype V] in
theorem sum_mem_ite (T : Finset V) [Fintype V] (f : V → ℝ) :
    ∑ p ∈ T, f p = ∑ p, if p ∈ T then f p else 0 := by
  rw [← sum_filter]; congr 1; ext; simp

/-- Each ordered minority triple lies in at most one minority triangle. -/
theorem minS_sum_le (g : V → V → V → ℝ) (hg : ∀ p q r, 0 ≤ g p q r)
    (hg0 : ∀ p q r, ¬ okM lab p q r → g p q r = 0) :
    ∑ T ∈ minS lab, ∑ p ∈ T, ∑ q ∈ T, ∑ r ∈ T, g p q r ≤ ∑ p, ∑ q, ∑ r, g p q r := by
  have e1 : ∀ T : Finset V, ∑ p ∈ T, ∑ q ∈ T, ∑ r ∈ T, g p q r =
      ∑ p, ∑ q, ∑ r, if p ∈ T ∧ q ∈ T ∧ r ∈ T then g p q r else 0 := by
    intro T
    rw [sum_mem_ite]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_mem_ite, ite_sum_zero]
    refine sum_congr rfl fun q _ => ?_
    rw [sum_mem_ite, ite_sum_zero, ite_sum_zero]
    refine sum_congr rfl fun r _ => ?_
    by_cases hp : p ∈ T <;> by_cases hq : q ∈ T <;> by_cases hr : r ∈ T <;> simp [hp, hq, hr]
  simp only [e1]
  rw [sum_comm]
  refine sum_le_sum fun p _ => ?_
  rw [sum_comm]
  refine sum_le_sum fun q _ => ?_
  rw [sum_comm]
  refine sum_le_sum fun r _ => ?_
  simp only [mem_univ, and_self, if_true]
  by_cases hok : okM lab p q r
  · obtain ⟨hpq, hq, hr⟩ := hok
    have hpr : p ≠ r := fun h => fin3_add2_ne (lab p) (by rw [← hr, h])
    have hqr : q ≠ r := fun h => fin3_add2_ne (lab p) (by rw [← hr, ← h, hq])
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hc : #((minS lab).filter fun T => p ∈ T ∧ q ∈ T ∧ r ∈ T) ≤ 1 := by
      refine card_le_one.2 fun T₁ h₁ T₂ h₂ => ?_
      have k : ∀ T ∈ (minS lab).filter (fun T => p ∈ T ∧ q ∈ T ∧ r ∈ T), T = {p, q, r} := by
        intro T hT
        obtain ⟨hT, hp, hq, hr⟩ := mem_filter.1 hT
        have h3 : T.card = 3 := ((gmem_tri.1 (mem_filter.1 hT).1).1)
        symm
        refine eq_of_subset_of_card_le ?_ ?_
        · intro y hy; simp only [mem_insert, mem_singleton] at hy
          rcases hy with rfl | rfl | rfl <;> assumption
        · rw [h3, card_eq_three.mpr ⟨p, q, r, hpq, hpr, hqr, rfl⟩]
      rw [k T₁ h₁, k T₂ h₂]
    have : (#((minS lab).filter fun T => p ∈ T ∧ q ∈ T ∧ r ∈ T) : ℝ) ≤ 1 := by exact_mod_cast hc
    nlinarith [hg p q r]
  · rw [hg0 p q r hok]; simp

theorem sum6_cov5 (T' : Finset V) :
    ∑ p, ∑ _q : V, ∑ r, ∑ x, ∑ w₁, ∑ w₂, cov5 T' ![r, p, x, w₁, w₂] =
      (Fintype.card V : ℝ) * ∑ t : Fin 5 → V, cov5 T' t := by
  have h1 : ∀ p : V, ∑ _q : V, ∑ r, ∑ x, ∑ w₁, ∑ w₂, cov5 T' ![r, p, x, w₁, w₂] =
      (Fintype.card V : ℝ) * ∑ r, ∑ x, ∑ w₁, ∑ w₂, cov5 T' ![r, p, x, w₁, w₂] := by
    intro p; rw [sum_const, card_univ, nsmul_eq_mul]
  rw [sum_congr rfl fun p _ => h1 p, ← mul_sum]
  congr 1
  rw [← sum_five (cov5 T')]
  exact Finset.sum_comm

/-- The constant of `Ψ₃`. -/
def C3 (n m : ℕ) : ℝ := 1 + 27 * n / (2 * (m : ℝ)) + 750 * (n : ℝ) ^ 3 * kapM m

/-- **The bound on `Ψ₃`.** -/
theorem abs_Psi3_le {m : ℕ} (hm : ∀ k, m ≤ csz lab k) (h3 : 3 ≤ m) {c : Finset V → ℝ} {β : ℝ}
    (hβ : ∀ T, |c T| ≤ β) (T' : Finset V) :
    |Psi3 lab c T'| ≤ C3 (Fintype.card V) m * β := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hβ0 : 0 ≤ β := (abs_nonneg _).trans (hβ T')
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk0 : 0 ≤ kapM m := by unfold kapM; positivity
  simp only [Psi3, LinearMap.coe_mk, AddHom.coe_mk]
  refine (abs_add_le _ _).trans ?_
  have h1 : |(if T' ∈ triG lab majF then c T' else 0)| ≤ β := by
    split_ifs
    · exact hβ T'
    · simpa using hβ0
  -- the minority part
  set G : V → V → V → ℝ := fun p q r => if okM lab p q r then |phi lab p q r T'| else 0 with hG
  have hpsi : ∀ T, |psiT lab T T'| ≤ ∑ p ∈ T, ∑ q ∈ T, ∑ r ∈ T, G p q r := by
    intro T
    unfold psiT
    simp only [Finset.sum_apply]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q _ => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
    simp only [hG]
    split_ifs <;> simp
  have hGn : ∀ p q r, 0 ≤ G p q r := fun p q r => by simp only [hG]; split_ifs <;> simp
  have hG0 : ∀ p q r, ¬ okM lab p q r → G p q r = 0 := fun p q r h => by simp [hG, h]
  have hsum : ∑ p, ∑ q, ∑ r, G p q r ≤ 27 * n / (2 * (m : ℝ)) + 750 * n ^ 3 * kapM m := by
    have hb : ∀ p q r, G p q r ≤ (1 / (2 * (m : ℝ))) * ∑ z, dX T' p q z +
        6 * kapM m * ∑ x, ∑ w₁, ∑ w₂, cov5 T' ![r, p, x, w₁, w₂] := by
      intro p q r
      simp only [hG]
      split_ifs with hok
      · exact abs_phi_le lab hm h3 hok T'
      · exact add_nonneg (mul_nonneg (by positivity) (sum_nonneg fun _ _ => dX_nonneg _ _ _ _))
          (mul_nonneg (by positivity) (sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
            sum_nonneg fun _ _ => cov5_nonneg _ _))
    refine (sum_le_sum fun p _ => sum_le_sum fun q _ => sum_le_sum fun r _ => hb p q r).trans ?_
    simp only [sum_add_distrib, ← mul_sum]
    have hA : ∑ p, ∑ q, ∑ _r : V, ∑ z, dX T' p q z = n * ∑ p, ∑ q, ∑ z, dX T' p q z := by
      rw [mul_sum]; refine sum_congr rfl fun p _ => ?_
      rw [mul_sum]; refine sum_congr rfl fun q _ => ?_
      rw [sum_const, card_univ, nsmul_eq_mul]
    have hB : ∑ p, ∑ _q : V, ∑ r, ∑ x, ∑ w₁, ∑ w₂, cov5 T' ![r, p, x, w₁, w₂] =
        n * ∑ t : Fin 5 → V, cov5 T' t := sum6_cov5 T'
    have hA' := sum_dX_le T'
    have hB' := sum_cov5_le T'
    rw [hA, hB]
    have e1 : 1 / (2 * (m : ℝ)) * (n * ∑ p, ∑ q, ∑ z, dX T' p q z) ≤ 27 * n / (2 * (m : ℝ)) := by
      rw [show 27 * n / (2 * (m : ℝ)) = 1 / (2 * (m : ℝ)) * (n * 27) by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA' (by positivity))
        (by positivity)
    have e2 : 6 * kapM m * (n * ∑ t : Fin 5 → V, cov5 T' t) ≤ 750 * n ^ 3 * kapM m := by
      have := mul_le_mul_of_nonneg_left hB' (show (0 : ℝ) ≤ 6 * kapM m * n by positivity)
      nlinarith
    linarith
  have h2 : |∑ T ∈ minS lab, c T * psiT lab T T'| ≤
      (27 * n / (2 * (m : ℝ)) + 750 * n ^ 3 * kapM m) * β := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ T ∈ minS lab, |c T * psiT lab T T'|
        ≤ ∑ T ∈ minS lab, β * ∑ p ∈ T, ∑ q ∈ T, ∑ r ∈ T, G p q r := by
          refine sum_le_sum fun T _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hβ T) (hpsi T) (abs_nonneg _) hβ0
      _ = β * ∑ T ∈ minS lab, ∑ p ∈ T, ∑ q ∈ T, ∑ r ∈ T, G p q r := by rw [mul_sum]
      _ ≤ β * ∑ p, ∑ q, ∑ r, G p q r :=
          mul_le_mul_of_nonneg_left (minS_sum_le lab G hGn hG0) hβ0
      _ ≤ β * (27 * n / (2 * (m : ℝ)) + 750 * n ^ 3 * kapM m) :=
          mul_le_mul_of_nonneg_left hsum hβ0
      _ = _ := by ring
  unfold C3
  linarith

/-- **The bounded right inverse of the majority incidence on `ker π`.** -/
def bri3 {K : ℝ} (B : BRIG lab cdrF (wl lab) K) {m : ℕ} (hm : ∀ k, m ≤ csz lab k) (h3 : 3 ≤ m) :
    BRIM lab majF (fun v => wpi lab v) (C3 (Fintype.card V) m * K) where
  Φ := Psi3 lab ∘ₗ B.Φ
  exact d hd := by
    rw [LinearMap.comp_apply, Minc_Psi3 lab (fun k => h3.trans (hm k)), B.exact d (ell_of_pi lab hd)]
    simp [hd]
  bound d hd T := by
    have h := abs_Psi3_le lab hm h3 (β := K / Fintype.card V * ‖d‖)
      (fun T' => B.bound d (ell_of_pi lab hd) T') T
    rw [LinearMap.comp_apply]
    refine h.trans (le_of_eq ?_)
    ring

end CDRBicolour.Absorption.Corners
