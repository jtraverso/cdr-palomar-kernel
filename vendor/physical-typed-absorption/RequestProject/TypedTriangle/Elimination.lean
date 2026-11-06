/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ElimPivots

@[expose] public section

/-!
# G1-Z, §6 de la guía V5 — Eliminación lineal por cinco eventos

`compression_of_sample`: de una salida muestral `SampleOut` (interfaz condicional de §5),
de H3, H4 y las ventanas sobre `|Z|` y `d`, se construyen homomorfismos `C₀, P` sobre
`M_H = localGroup H F` con

  `x − P x = A C₀(x)`,   `soporte(P x) ⊆ E(W)`,
  `‖C₀ x‖₁ ≤ H₀‖x‖₁`,   `‖P x‖₁ ≤ D₀‖x‖₁`,

donde `H₀ = compH0 α s`, `D₀ = compD0 α s` sólo dependen de `α` y `s` (no de `n`, del host,
de la demanda ni de un certificado previo). Los cinco eventos, todos fijados antes de `x`:

1. pivotes para las aristas internas de `Z` (tercero fuera de `Z`);
2. estrellas de raíces en `Z`, simultáneamente, con la sección de `L_v − Z` (diámetro
   uniforme `3⌊2/α⌋`, robustez de la imagen entera de `link_image_robust`);
3. pivotes para las aristas de `B` (otras aristas fuera de `B` y de `Z`);
4. pivotes para las demás aristas exteriores (tercero en `W`);
5. estrellas de los vértices exteriores, con la sección de `L_v[W]` (diámetro `≤ s`) y la
   igualdad de imágenes de la muestra.

Las constantes se multiplican una vez por evento, nunca por vértice.

`uniformCert_of_sample` compone con `g1z_of_compression`: G1-Z queda reducido EXACTAMENTE a
la existencia de la muestra (interfaz `SampleOut` con las ventanas), que no se construye aquí.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence

variable {V I : Type*} [Fintype V] {H : Host V I} {F : Set (Multiset I)}

/-- Submódulo de las cargas que se anulan en las aristas que cumplen `P`. -/
def vanishOn (P : Sym2 V → Prop) : Submodule ℤ (Sym2 V → ℤ) where
  carrier := {x | ∀ e, P e → x e = 0}
  add_mem' hx hy e he := by simp [hx e he, hy e he]
  zero_mem' _ _ := rfl
  smul_mem' k x hx e he := by simp [hx e he]

omit [Fintype V] in
lemma mem_vanishOn {P : Sym2 V → Prop} {x : Sym2 V → ℤ} :
    x ∈ vanishOn P ↔ ∀ e, P e → x e = 0 := Iff.rfl

/-- `e` toca `Z`. -/
def TouchZ (Z : Finset V) (e : Sym2 V) : Prop := ∃ z ∈ Z, z ∈ e

omit [Fintype V] in
lemma not_hasTri_diag (y : V) : ¬ HasTri H F s(y, y) := by
  rintro ⟨T, -, hT⟩
  exact (mem_triEdges.1 hT).2.2 rfl

lemma sum_abs_add_le (f g : Finset V → ℤ) :
    ∑ T, |(f + g) T| ≤ ∑ T, |f T| + ∑ T, |g T| := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun T _ => abs_add_le _ _

/-- Paso final del evento 5: el residuo queda soportado en `E(W)`. -/
lemma event5_vanish {W Z : Finset V} (hWZ : Disjoint W Z) {x : Sym2 V → ℤ}
    (hx : ∀ e, (TouchZ Z e ∨ ∀ y ∈ e, y ∉ W) → x e = 0) {c : Finset V → ℤ}
    (hsupp : ∀ T, c T ≠ 0 → ∃ v ∈ univ.filter (fun v => v ∉ W ∧ v ∉ Z), ∃ a b,
      (linkOn H F v W.sym2).Adj a b ∧ T = {v, a, b})
    (hstar : ∀ v ∈ univ.filter (fun v => v ∉ W ∧ v ∉ Z),
      starProj v (x - triBd H F c) = 0) :
    ∀ e, e ∉ W.sym2 → (x - triBd H F c) e = 0 := by
  have hW5 : ∀ v a b, (linkOn H F v W.sym2).Adj a b → a ∈ W := fun v a b hab =>
    Finset.mem_sym2_iff.1 hab.2 a (by simp)
  intro e he
  by_contra hne
  by_cases hbad : TouchZ Z e ∨ ∀ y ∈ e, y ∉ W
  · have hx0 : x e = 0 := hx e hbad
    have htb : triBd H F c e ≠ 0 := by
      intro h0; apply hne; rw [Pi.sub_apply, hx0, h0, sub_zero]
    obtain ⟨T, -, hcT, heT⟩ := triBd_support htb
    obtain ⟨v, hvR, a, b, hab, hT⟩ := hsupp T hcT
    rw [hT] at heT
    obtain ⟨-, hvW, hvZ⟩ := Finset.mem_filter.1 hvR
    have haW := hW5 v a b hab
    have hbW := hW5 v b a hab.symm
    have haZ : a ∉ Z := Finset.disjoint_left.1 hWZ haW
    have hbZ : b ∉ Z := Finset.disjoint_left.1 hWZ hbW
    rcases hbad with ⟨z, hz, hze⟩ | hW
    · have hzT : z ∈ ({v, a, b} : Finset V) := by
        induction e using Sym2.ind with
        | _ p q =>
        obtain ⟨hp, hq, -⟩ := mem_triEdges.1 heT
        rcases Sym2.mem_iff.1 hze with h | h
        · exact h ▸ hp
        · exact h ▸ hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzT
      rcases hzT with h | h | h
      · exact hvZ (h ▸ hz)
      · exact haZ (h ▸ hz)
      · exact hbZ (h ▸ hz)
    · rcases mem_triEdges_tri heT with h | h | h
      · exact hW a (by rw [h]; simp) haW
      · exact hW b (by rw [h]; simp) hbW
      · exact hW a (by rw [h]; simp) haW
  · push_neg at hbad
    obtain ⟨hnZ, w, hwe, hwW⟩ := hbad
    induction e using Sym2.ind with
    | _ p q =>
    obtain ⟨y, hey⟩ : ∃ y, s(p, q) = s(w, y) := by
      rcases Sym2.mem_iff.1 hwe with h | h
      · exact ⟨q, by rw [h]⟩
      · exact ⟨p, by rw [h, Sym2.eq_swap]⟩
    rw [hey] at he hne hnZ
    have hyW : y ∉ W := fun hyW => he (Finset.mem_sym2_iff.2 fun a ha => by
      rcases Sym2.mem_iff.1 ha with h | h
      · exact h ▸ hwW
      · exact h ▸ hyW)
    have hyZ : y ∉ Z := fun hyZ => hnZ ⟨y, hyZ, by simp⟩
    have hyR : y ∈ univ.filter (fun v => v ∉ W ∧ v ∉ Z) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hyW, hyZ⟩
    have hwy : w ≠ y := fun h' => hyW (h' ▸ hwW)
    have := congrFun (hstar y hyR) w
    rw [starProj_apply, if_neg hwy, Sym2.eq_swap] at this
    exact hne this

/-- Constantes de la compresión. -/
def compL2 (α : ℝ) : ℕ := 2 * (3 * ⌊2 / α⌋₊) + 1
def compL5 (s : ℕ) : ℕ := 2 * s + 1
def compN (α : ℝ) : ℕ := 4 + 24 * compL2 α
def compH0 (α : ℝ) (s : ℕ) : ℕ := 1 + 8 * compL2 α + 5 * compN α + 32 * compL5 s * compN α
def compD0 (α : ℝ) (s : ℕ) : ℕ := 16 * compN α + 96 * compL5 s * compN α

/-- **Eliminación lineal (§6): compresión desde la muestra.** -/
theorem compression_of_sample {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) {s d : ℕ} (smp : SampleOut H F s d)
    (hw1 : (smp.Z.card : ℝ) + 2 + 4 * d < α * Fintype.card V)
    (hw2 : ((smp.Z.card : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V)
    (hw3 : (smp.Z.card : ℝ) + d ≤ α * Fintype.card V / 2) :
    Nonempty (Compression H F s (compH0 α s) (compD0 α s)) := by
  set W := smp.W
  set Z := smp.Z
  set B := smp.B
  have hd0 : (0 : ℝ) ≤ d := by positivity
  set L := localGroup H F
  -- submódulos de las etapas
  set M1 := L ⊓ vanishOn (· ∈ Z.sym2)
  set M2 := L ⊓ vanishOn (TouchZ Z)
  set M3 := M2 ⊓ vanishOn (· ∈ B)
  set M4 := L ⊓ vanishOn (fun e => TouchZ Z e ∨ ∀ y ∈ e, y ∉ W)
  set M5 : Submodule ℤ (Sym2 V → ℤ) := vanishOn (· ∉ W.sym2)
  ------------------------------------------------------------------ evento 1
  have hZ1 : (Z.card : ℝ) < α * Fintype.card V := by linarith
  set ps1 := piv1 hH3 Z hZ1
  have he1 : ∀ x : L, pivF ps1 x.1 ∈ M1 := by
    intro x
    refine ⟨pivF_mem ps1 x.2, fun e he => ?_⟩
    by_cases hS : e ∈ S1 H F Z
    · exact pivF_apply_mem ps1 x.1 hS
    · have hT : ¬ HasTri H F e := fun hT => hS (Finset.mem_filter.2 ⟨Finset.mem_univ _, he, hT⟩)
      exact localGroup_zero_of_not_hasTri (pivF_mem ps1 x.2) hT
  let e1 : L →ₗ[ℤ] M1 := LinearMap.codRestrict M1 ((pivL ps1).comp L.subtype) he1
  let c1 : L →ₗ[ℤ] (Finset V → ℤ) := (pivC ps1).comp L.subtype
  have hs1 : ∀ x : L, x.1 - (e1 x).1 = triBd H F (c1 x) := fun x => by
    change x.1 - pivF ps1 x.1 = _; simp [pivF, c1]
  have hc1 : ∀ x : L, ∑ T, |c1 x T| ≤ l1E x.1 := fun x => sum_abs_pivC_le ps1 x.1
  have hn1 : ∀ x : L, l1E (e1 x).1 ≤ 4 * l1E x.1 := fun x => l1E_pivF_le ps1 x.1
  ------------------------------------------------------------------ evento 2
  set D2 := 3 * ⌊2 / α⌋₊
  let G2 : V → SimpleGraph V := fun v => linkOn H F v (goodEdges H (Z.erase v) ∅)
  have hdeg0 : ∀ x, degIn (∅ : Finset (Sym2 V)) x ≤ 0 := fun x => by simp [degIn]
  have hcardE : ∀ v, ((Z.erase v).card : ℝ) ≤ Z.card := fun v => by
    exact_mod_cast Finset.card_erase_le
  obtain ⟨c2, hc2⟩ := star_event (M := M1) (H := H) (F := F) Z G2
    (fun v _ a b hab => hab.1)
    (by
      intro v _ a b hab hav
      have hgood := (Finset.mem_filter.1 (Finset.mem_filter.1 hab.2).1).2
      have hva : v ≠ a := (linkGraph_adj_ne hab.1).1
      exact hgood a (Finset.mem_erase.2 ⟨Ne.symm hva, hav⟩) (by simp))
    (D := D2)
    (fun v _ => linkOn_good_diamLe hα hH3 v (Z.erase v) ∅ hdeg0
      (by push_cast; linarith [hcardE v]))
    (by
      intro x hx v hv
      have hvan : ∀ y ∈ Z.erase v, starProj v x y = 0 := by
        intro y hy
        rw [starProj_apply, if_neg (Finset.ne_of_mem_erase hy)]
        exact hx.2 _ (Finset.mem_sym2_iff.2 fun a ha => by
          rcases Sym2.mem_iff.1 ha with rfl | rfl
          · exact hv
          · exact Finset.mem_of_mem_erase hy)
      refine (link_image_robust hα hH3 hH4 (Z.erase v) (by simp) ∅ 0 hdeg0
        (by push_cast; linarith [hcardE v]) (by
          push_cast
          refine le_trans ?_ hw2
          have : (0 : ℝ) ≤ 2 ^ Nat.choose h 2 := by positivity
          nlinarith [hcardE v]) hvan).1 (starProj_mem_of_localGroup hx.1 v))
  have he2 : ∀ x : M1, x.1 - triBd H F (c2 x) ∈ M2 := by
    intro x
    refine ⟨Submodule.sub_mem _ x.2.1 (triBd_mem_localGroup H F _), fun e he => ?_⟩
    obtain ⟨z, hz, hze⟩ := he
    obtain ⟨-, hstar, -⟩ := hc2 x
    induction e using Sym2.ind with
    | _ a b =>
    have hmem := Submodule.sub_mem _ x.2.1 (triBd_mem_localGroup H F (c2 x))
    obtain ⟨y, hey⟩ : ∃ y, s(a, b) = s(z, y) := by
      rcases Sym2.mem_iff.1 hze with rfl | rfl
      · exact ⟨b, rfl⟩
      · exact ⟨a, Sym2.eq_swap⟩
    rw [hey]
    by_cases hyz : y = z
    · subst hyz; exact localGroup_zero_of_not_hasTri hmem (not_hasTri_diag y)
    · have := congrFun (hstar z hz) y
      rwa [starProj_apply, if_neg hyz] at this
  let e2 : M1 →ₗ[ℤ] M2 := LinearMap.codRestrict M2 (M1.subtype - (triBd H F).comp c2) he2
  have hs2 : ∀ x : M1, x.1 - (e2 x).1 = triBd H F (c2 x) := fun x => by
    change x.1 - (x.1 - triBd H F (c2 x)) = _; abel
  have hcc2 : ∀ x : M1, ∑ T, |c2 x T| ≤ compL2 α * (2 * l1E x.1) := fun x => by
    have := (hc2 x).2.2; simpa [compL2, D2] using this
  have hn2 : ∀ x : M1, l1E (e2 x).1 ≤ l1E x.1 + 3 * (compL2 α * (2 * l1E x.1)) := fun x => by
    change l1E (x.1 - triBd H F (c2 x)) ≤ _
    have := l1E_sub_le x.1 (triBd H F (c2 x))
    have := l1E_triBd_le H F (c2 x)
    linarith [hcc2 x]
  ------------------------------------------------------------------ evento 3
  have hZ3 : (Z.card : ℝ) + 2 * d < α * Fintype.card V := by linarith
  set ps3 := piv3 hH3 Z B (fun e he y hy => (smp.B_out e he y hy).2) smp.B_deg hZ3
  have he3 : ∀ x : M2, pivF ps3 x.1 ∈ M3 := by
    intro x
    have hL := pivF_mem ps3 x.2.1
    refine ⟨⟨hL, fun e he => ?_⟩, fun e he => ?_⟩
    · by_contra hne
      obtain ⟨z, hz, hze⟩ := he
      rcases pivF_support ps3 x.1 hne with h1 | ⟨e'', he'', -, heT⟩
      · exact h1 (x.2.2 e ⟨z, hz, hze⟩)
      · by_cases hee : e = e''
        · subst hee
          exact (smp.B_out e (Finset.mem_filter.1 he'').1 z hze).2 hz
        · have := piv3_good hH3 Z B (fun e he y hy => (smp.B_out e he y hy).2) smp.B_deg hZ3 he''
          exact (this e heT hee).2 z hze hz
    · by_cases hT : HasTri H F e
      · exact pivF_apply_mem ps3 x.1 (Finset.mem_filter.2 ⟨he, hT⟩)
      · exact localGroup_zero_of_not_hasTri hL hT
  let e3 : M2 →ₗ[ℤ] M3 := LinearMap.codRestrict M3 ((pivL ps3).comp M2.subtype) he3
  let c3 : M2 →ₗ[ℤ] (Finset V → ℤ) := (pivC ps3).comp M2.subtype
  have hs3 : ∀ x : M2, x.1 - (e3 x).1 = triBd H F (c3 x) := fun x => by
    change x.1 - pivF ps3 x.1 = _; simp [pivF, c3]
  have hcc3 : ∀ x : M2, ∑ T, |c3 x T| ≤ l1E x.1 := fun x => sum_abs_pivC_le ps3 x.1
  have hn3 : ∀ x : M2, l1E (e3 x).1 ≤ 4 * l1E x.1 := fun x => l1E_pivF_le ps3 x.1
  ------------------------------------------------------------------ evento 4
  set ps4 := piv4 smp
  have he4 : ∀ x : M3, pivF ps4 x.1 ∈ M4 := by
    intro x
    have hL := pivF_mem ps4 x.2.1.1
    refine ⟨hL, fun e he => ?_⟩
    by_contra hne
    rcases pivF_support ps4 x.1 hne with h1 | ⟨e'', he'', -, heT⟩
    · -- `x e ≠ 0`: `e` no toca `Z`, no está en `B` y tiene triángulo
      have hnZ : ¬ TouchZ Z e := fun hz => h1 (x.2.1.2 e hz)
      have hnB : e ∉ B := fun hb => h1 (x.2.2 e hb)
      have hT := hasTri_of_ne x.2.1.1 h1
      rcases he with hz | hW
      · exact hnZ hz
      · have hS : e ∈ S4 H F W Z B := Finset.mem_filter.2 ⟨Finset.mem_univ _, hT, hnB,
          fun y hy => ⟨hW y hy, fun hyZ => hnZ ⟨y, hyZ, hy⟩⟩⟩
        exact hne (pivF_apply_mem ps4 x.1 hS)
    · have hG := piv4_good smp he''
      rcases he with ⟨z, hz, hze⟩ | hW
      · have hzT : z ∈ ps4.piv e'' := by
          induction e using Sym2.ind with
          | _ a b =>
          obtain ⟨ha, hb, -⟩ := mem_triEdges.1 heT
          rcases Sym2.mem_iff.1 hze with rfl | rfl
          · exact ha
          · exact hb
        exact hG.1 z hzT hz
      · by_cases hee : e = e''
        · subst hee; exact hne (pivF_apply_mem ps4 x.1 he'')
        · obtain ⟨y, hy, hyW⟩ := hG.2 e heT hee
          exact hW y hy hyW
  let e4 : M3 →ₗ[ℤ] M4 := LinearMap.codRestrict M4 ((pivL ps4).comp M3.subtype) he4
  let c4 : M3 →ₗ[ℤ] (Finset V → ℤ) := (pivC ps4).comp M3.subtype
  have hs4 : ∀ x : M3, x.1 - (e4 x).1 = triBd H F (c4 x) := fun x => by
    change x.1 - pivF ps4 x.1 = _; simp [pivF, c4]
  have hcc4 : ∀ x : M3, ∑ T, |c4 x T| ≤ l1E x.1 := fun x => sum_abs_pivC_le ps4 x.1
  have hn4 : ∀ x : M3, l1E (e4 x).1 ≤ 4 * l1E x.1 := fun x => l1E_pivF_le ps4 x.1
  ------------------------------------------------------------------ evento 5
  set R := univ.filter (fun v => v ∉ W ∧ v ∉ Z)
  let G5 : V → SimpleGraph V := fun v => linkOn H F v W.sym2
  have hW5 : ∀ v a b, (G5 v).Adj a b → a ∈ W := fun v a b hab =>
    Finset.mem_sym2_iff.1 hab.2 a (by simp)
  obtain ⟨c5, hc5⟩ := star_event (M := M4) (H := H) (F := F) R G5
    (fun v _ a b hab => hab.1)
    (fun v _ a b hab haR => (Finset.mem_filter.1 haR).2.1 (hW5 v a b hab))
    (D := s)
    (by
      intro v _ u w huw
      obtain ⟨p, hp⟩ := diamLe_of_adj_mem (hW5 v) u w huw
      exact ⟨p, hp.trans smp.card_W⟩)
    (by
      intro x hx v hv
      obtain ⟨-, hvW, hvZ⟩ := Finset.mem_filter.1 hv
      refine smp.image v hvW hvZ _ (fun y hy => ?_) (starProj_mem_of_localGroup hx.1 v)
      rw [starProj_apply]
      split_ifs with hyv
      · rfl
      · exact hx.2 _ (Or.inr fun y' hy' => by
          rcases Sym2.mem_iff.1 hy' with rfl | rfl
          · exact hvW
          · exact hy))
  have he5 : ∀ x : M4, x.1 - triBd H F (c5 x) ∈ M5 := by
    intro x
    obtain ⟨hsupp, hstar, -⟩ := hc5 x
    exact event5_vanish smp.disj (fun e he => x.2.2 e he) hsupp hstar
  let e5 : M4 →ₗ[ℤ] M5 := LinearMap.codRestrict M5 (M4.subtype - (triBd H F).comp c5) he5
  have hs5 : ∀ x : M4, x.1 - (e5 x).1 = triBd H F (c5 x) := fun x => by
    change x.1 - (x.1 - triBd H F (c5 x)) = _; abel
  have hcc5 : ∀ x : M4, ∑ T, |c5 x T| ≤ compL5 s * (2 * l1E x.1) := fun x => by
    have := (hc5 x).2.2; simpa [compL5] using this
  have hn5 : ∀ x : M4, l1E (e5 x).1 ≤ l1E x.1 + 3 * (compL5 s * (2 * l1E x.1)) := fun x => by
    change l1E (x.1 - triBd H F (c5 x)) ≤ _
    have := l1E_sub_le x.1 (triBd H F (c5 x))
    have := l1E_triBd_le H F (c5 x)
    linarith [hcc5 x]
  ------------------------------------------------------------------ composición
  let Q1 := e1
  let Q2 := e2.comp Q1
  let Q3 := e3.comp Q2
  let Q4 := e4.comp Q3
  let Q5 := e5.comp Q4
  let P : L →ₗ[ℤ] (Sym2 V → ℤ) := M5.subtype.comp Q5
  let C₀ : L →ₗ[ℤ] (Finset V → ℤ) :=
    c1 + c2.comp Q1 + c3.comp Q2 + c4.comp Q3 + c5.comp Q4
  refine ⟨⟨W, smp.card_W, C₀, P, ?_, ?_, ?_, ?_⟩⟩
  · intro x
    have h1 : x.1 - (Q1 x).1 = triBd H F (c1 x) := hs1 x
    have h2 : (Q1 x).1 - (Q2 x).1 = triBd H F (c2 (Q1 x)) := hs2 (Q1 x)
    have h3 : (Q2 x).1 - (Q3 x).1 = triBd H F (c3 (Q2 x)) := hs3 (Q2 x)
    have h4 : (Q3 x).1 - (Q4 x).1 = triBd H F (c4 (Q3 x)) := hs4 (Q3 x)
    have h5 : (Q4 x).1 - (Q5 x).1 = triBd H F (c5 (Q4 x)) := hs5 (Q4 x)
    show x.1 - (Q5 x).1 =
      triBd H F (c1 x + c2 (Q1 x) + c3 (Q2 x) + c4 (Q3 x) + c5 (Q4 x))
    rw [map_add, map_add, map_add, map_add, ← h1, ← h2, ← h3, ← h4, ← h5]
    abel
  · intro x e he
    by_contra hW
    exact he ((Q5 x).2 e hW)
  · intro x
    set k := l1E x.1
    have hk : 0 ≤ k := l1E_nonneg _
    have hL2 : (0 : ℤ) ≤ compL2 α := by positivity
    have hL5 : (0 : ℤ) ≤ compL5 s := by positivity
    have hN : (0 : ℤ) ≤ compN α := by positivity
    have n1 : l1E (Q1 x).1 ≤ 4 * k := hn1 x
    have a1 := hc1 x
    have a2 : ∑ T, |c2 (Q1 x) T| ≤ compL2 α * (2 * l1E (Q1 x).1) := hcc2 (Q1 x)
    have n2 : l1E (Q2 x).1 ≤ l1E (Q1 x).1 + 3 * (compL2 α * (2 * l1E (Q1 x).1)) :=
      hn2 (Q1 x)
    have a3 : ∑ T, |c3 (Q2 x) T| ≤ l1E (Q2 x).1 := hcc3 (Q2 x)
    have n3 : l1E (Q3 x).1 ≤ 4 * l1E (Q2 x).1 := hn3 (Q2 x)
    have a4 : ∑ T, |c4 (Q3 x) T| ≤ l1E (Q3 x).1 := hcc4 (Q3 x)
    have n4 : l1E (Q4 x).1 ≤ 4 * l1E (Q3 x).1 := hn4 (Q3 x)
    have a5 : ∑ T, |c5 (Q4 x) T| ≤ compL5 s * (2 * l1E (Q4 x).1) := hcc5 (Q4 x)
    have hsum : ∑ T, |C₀ x T| ≤ ∑ T, |c1 x T| + ∑ T, |c2 (Q1 x) T| + ∑ T, |c3 (Q2 x) T| +
        ∑ T, |c4 (Q3 x) T| + ∑ T, |c5 (Q4 x) T| := by
      change ∑ T, |(c1 x + c2 (Q1 x) + c3 (Q2 x) + c4 (Q3 x) + c5 (Q4 x)) T| ≤ _
      have := sum_abs_add_le (c1 x + c2 (Q1 x) + c3 (Q2 x) + c4 (Q3 x)) (c5 (Q4 x))
      have := sum_abs_add_le (c1 x + c2 (Q1 x) + c3 (Q2 x)) (c4 (Q3 x))
      have := sum_abs_add_le (c1 x + c2 (Q1 x)) (c3 (Q2 x))
      have := sum_abs_add_le (c1 x) (c2 (Q1 x))
      linarith
    have b2 : l1E (Q2 x).1 ≤ compN α * k := by
      simp only [compN]; push_cast; nlinarith
    have b3 : l1E (Q3 x).1 ≤ 4 * (compN α * k) := by linarith
    have b4 : l1E (Q4 x).1 ≤ 16 * (compN α * k) := by linarith
    simp only [compH0]; push_cast
    nlinarith
  · intro x
    set k := l1E x.1
    have hk : 0 ≤ k := l1E_nonneg _
    have hL2 : (0 : ℤ) ≤ compL2 α := by positivity
    have hL5 : (0 : ℤ) ≤ compL5 s := by positivity
    have hN : (0 : ℤ) ≤ compN α := by positivity
    have n1 : l1E (Q1 x).1 ≤ 4 * k := hn1 x
    have n2 : l1E (Q2 x).1 ≤ l1E (Q1 x).1 + 3 * (compL2 α * (2 * l1E (Q1 x).1)) :=
      hn2 (Q1 x)
    have n3 : l1E (Q3 x).1 ≤ 4 * l1E (Q2 x).1 := hn3 (Q2 x)
    have n4 : l1E (Q4 x).1 ≤ 4 * l1E (Q3 x).1 := hn4 (Q3 x)
    have n5 : l1E (Q5 x).1 ≤ l1E (Q4 x).1 + 3 * (compL5 s * (2 * l1E (Q4 x).1)) :=
      hn5 (Q4 x)
    have b2 : l1E (Q2 x).1 ≤ compN α * k := by
      simp only [compN]; push_cast; nlinarith
    have b3 : l1E (Q3 x).1 ≤ 4 * (compN α * k) := by linarith
    have b4 : l1E (Q4 x).1 ≤ 16 * (compN α * k) := by linarith
    show l1E (Q5 x).1 ≤ _
    simp only [compD0]; push_cast
    nlinarith

/-- **G1-Z reducido a la muestra.** Hay `K = K(α, s)` tal que toda salida muestral con las
ventanas da un certificado entero uniforme `‖c‖₁ ≤ K‖x‖₁` para todo `x ∈ Λ_H`. -/
theorem uniformCert_of_sample (α : ℝ) (s : ℕ) :
    ∃ K : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) {h d : ℕ},
      0 < α → CommonNbrCond H F α → HingeCond H F α h → ∀ smp : SampleOut H F s d,
      (smp.Z.card : ℝ) + 2 + 4 * d < α * Fintype.card V →
      ((smp.Z.card : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V →
      (smp.Z.card : ℝ) + d ≤ α * Fintype.card V / 2 → UniformCert H F K := by
  obtain ⟨K, hK⟩ := g1z_of_compression s (compH0 α s) (compD0 α s)
  refine ⟨K, fun {V I} _ H F h d hα hH3 hH4 smp hw1 hw2 hw3 => ?_⟩
  obtain ⟨cmp⟩ := compression_of_sample hα hH3 hH4 smp hw1 hw2 hw3
  exact hK H F cmp

end TypedTriangle
