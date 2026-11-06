/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.LinkDiameter
public import RequestProject.TypedTriangle.IntLift
public import RequestProject.TypedTriangle.SlotAbsorber

@[expose] public section

/-!
# G1-Z, §7 de la guía V5 — Catálogo ambiental y cierre de G1-Z desde una compresión lineal

* `triBd H F`: la incidencia física `A c = Σ_{T permitido} c_T 𝟏_{E(T)}`.
* `UniformCert H F K`: el enunciado de G1-Z con constante `K` — todo `x ∈ Λ_H` tiene un
  certificado entero `c` con `A c = x` y `‖c‖₁ ≤ K‖x‖₁`.
* `Compression H F s H₀ D₀`: la salida de la eliminación lineal de §6 — un núcleo `W` con
  `|W| ≤ s` y homomorfismos `C₀, P` definidos en `M_H = localGroup H F` con
  `x − P x = A C₀(x)`, `P x` soportado en `E(W)`, `‖C₀ x‖₁ ≤ H₀‖x‖₁`, `‖P x‖₁ ≤ D₀‖x‖₁`.
* `g1z_of_compression`: hay `K = K(s, H₀, D₀)` (independiente de `n`, del host y de todo
  certificado previo) tal que toda compresión da `UniformCert H F K`. La prueba usa
  realizadores AMBIENTALES `q_T = δ_T − C₀(A[T])` para las columnas residuales `P(A[T])`
  (no se afirma que pertenezcan al retículo de `H[W]`), la inclusión de coordenadas de
  `E(W)` en `ℤ^{(s+1)²}` que conserva la norma, `int_lift_uniform` y `recovery_splice`.
* `slot_absorber_of_uniformCert`: conexión con `slot_absorber_of_coeffs` — un certificado
  uniforme da el absorbedor terminal de un grafo físico `P` con `|A| ≤ K|P|(4C(2h−2,2)+6)`.

La existencia de la compresión (muestra `W, Z, B` y los cinco eventos) NO se supone aquí
como hipótesis del Teorema T: `Compression` es una interfaz condicional.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence

variable {V I : Type*} [Fintype V]

/-- Incidencia física: `A c = Σ_{T permitido} c_T 𝟏_{E(T)}`. -/
def triBd (H : Host V I) (F : Set (Multiset I)) : (Finset V → ℤ) →ₗ[ℤ] (Sym2 V → ℤ) where
  toFun c := ∑ T ∈ allowed H F, c T • ind (triEdges T)
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' k c := by simp [Finset.smul_sum, mul_smul]

lemma triBd_single {H : Host V I} {F : Set (Multiset I)} {T : Finset V}
    (hT : T ∈ allowed H F) : triBd H F (Pi.single T 1) = ind (triEdges T) := by
  change ∑ T' ∈ allowed H F, (Pi.single T 1 : Finset V → ℤ) T' • ind (triEdges T') = _
  rw [Finset.sum_eq_single T]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hT h

/-- **G1-Z con constante `K`.** -/
def UniformCert (H : Host V I) (F : Set (Multiset I)) (K : ℕ) : Prop :=
  ∀ x ∈ lattice H F, ∃ c : Finset V → ℤ, triBd H F c = x ∧ ∑ T, |c T| ≤ K * l1E x

/-- **Interfaz de compresión** (salida de la eliminación lineal de §6). -/
structure Compression (H : Host V I) (F : Set (Multiset I)) (s H₀ D₀ : ℕ) where
  W : Finset V
  card_W : W.card ≤ s
  C₀ : localGroup H F →ₗ[ℤ] (Finset V → ℤ)
  P : localGroup H F →ₗ[ℤ] (Sym2 V → ℤ)
  decomp : ∀ x, x.1 - P x = triBd H F (C₀ x)
  supp : ∀ x e, P x e ≠ 0 → e ∈ W.sym2
  costC : ∀ x, ∑ T, |C₀ x T| ≤ H₀ * l1E x.1
  costP : ∀ x, l1E (P x) ≤ D₀ * l1E x.1

omit [Fintype V] in
lemma l1E_ind_triEdges [Fintype V] {T : Finset V} (hT : T.card = 3) :
    l1E (ind (triEdges T)) = 3 := by
  simp only [l1E, ind]
  rw [show (∑ e : Sym2 V, |if e ∈ triEdges T then (1 : ℤ) else 0|) =
      ∑ e : Sym2 V, if e ∈ triEdges T then (1 : ℤ) else 0 from
    Finset.sum_congr rfl fun e _ => by split_ifs <;> simp]
  rw [Finset.sum_boole]
  simp [Finset.filter_mem_eq_inter, card_triEdges_three hT]

/-! ## Inclusión de coordenadas de `E(W)` -/

section Coords

variable (W : Finset V) {dm : ℕ} (hdm : W.sym2.card ≤ dm)

/-- Índice de una arista de `E(W)` en `Fin dm`. -/
def eIdx (e : W.sym2) : Fin dm := Fin.castLE hdm (W.sym2.equivFin e)

omit [Fintype V] in
lemma eIdx_injective : Function.Injective (eIdx W hdm) := by
  intro e e' h
  have := Fin.castLE_injective hdm h
  exact W.sym2.equivFin.injective this

/-- Inclusión `ℤ^{dm} → ℤ^E`. -/
def eEmb : (Fin dm → ℤ) →ₗ[ℤ] (Sym2 V → ℤ) where
  toFun y e := if h : e ∈ W.sym2 then y (eIdx W hdm ⟨e, h⟩) else 0
  map_add' y z := by
    funext e
    by_cases h : e ∈ W.sym2
    · simp only [Pi.add_apply, dif_pos h]
    · simp only [Pi.add_apply, dif_neg h, add_zero]
  map_smul' k y := by
    funext e
    by_cases h : e ∈ W.sym2
    · simp only [Pi.smul_apply, dif_pos h, RingHom.id_apply]
    · simp only [Pi.smul_apply, dif_neg h, smul_zero, RingHom.id_apply]

/-- Proyección `ℤ^E → ℤ^{dm}`. -/
def eProj : (Sym2 V → ℤ) →ₗ[ℤ] (Fin dm → ℤ) where
  toFun z j := ∑ e ∈ W.sym2.attach, if eIdx W hdm e = j then z e else 0
  map_add' y z := by
    funext j; simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp
  map_smul' k y := by
    funext j; simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp

omit [Fintype V] in
lemma eProj_apply_idx (z : Sym2 V → ℤ) (e : W.sym2) : eProj W hdm z (eIdx W hdm e) = z e := by
  change ∑ e' ∈ W.sym2.attach, (if eIdx W hdm e' = eIdx W hdm e then z e' else 0) = z e
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb; rw [if_neg (fun h => hb (eIdx_injective W hdm h))]
  · intro h; exact absurd (Finset.mem_attach _ e) h

omit [Fintype V] in
lemma eEmb_eProj {z : Sym2 V → ℤ} (hz : ∀ e, z e ≠ 0 → e ∈ W.sym2) :
    eEmb W hdm (eProj W hdm z) = z := by
  funext e
  change (if h : e ∈ W.sym2 then eProj W hdm z (eIdx W hdm ⟨e, h⟩) else 0) = z e
  split_ifs with h
  · exact eProj_apply_idx W hdm z ⟨e, h⟩
  · by_contra hne; exact h (hz e (Ne.symm hne))

lemma l1_eProj_le (z : Sym2 V → ℤ) : IntLift.l1 (eProj W hdm z) ≤ l1E z := by
  unfold IntLift.l1 l1E
  calc ∑ j, |eProj W hdm z j|
      ≤ ∑ j : Fin dm, ∑ e ∈ W.sym2.attach, (if eIdx W hdm e = j then |z e| else 0) := by
        refine Finset.sum_le_sum fun j _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact le_of_eq (Finset.sum_congr rfl fun e _ => by split_ifs <;> simp)
    _ = ∑ e ∈ W.sym2.attach, |z e| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun e _ => by simp
    _ ≤ ∑ e, |z e| := by
        rw [Finset.sum_attach W.sym2 (fun e => |z e|)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => abs_nonneg _

lemma abs_eProj_le (z : Sym2 V → ℤ) (j : Fin dm) : |eProj W hdm z j| ≤ l1E z := by
  refine le_trans ?_ (l1_eProj_le W hdm z)
  unfold IntLift.l1
  exact Finset.single_le_sum (f := fun j => |eProj W hdm z j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ j)

end Coords

/-! ## Cierre de G1-Z desde una compresión -/

omit [Fintype V] in
lemma card_sym2_le (W : Finset V) {s : ℕ} (hW : W.card ≤ s) : W.sym2.card ≤ (s + 1) ^ 2 := by
  rw [Finset.card_sym2]
  calc (W.card + 1).choose 2 ≤ (W.card + 1) ^ 2 := by
        rw [Nat.choose_two_right]
        exact (Nat.div_le_self _ _).trans (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    _ ≤ (s + 1) ^ 2 := by gcongr

/-- **G1-Z desde una compresión lineal (catálogo ambiental + decoder entero).** -/
theorem g1z_of_compression (s H₀ D₀ : ℕ) :
    ∃ K : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
      Compression H F s H₀ D₀ → UniformCert H F K := by
  obtain ⟨K₀, hK₀⟩ := IntLift.recovery_splice ((s + 1) ^ 2) (3 * D₀)
  refine ⟨H₀ + (1 + 3 * H₀) * K₀ * D₀, fun {V I} _ H F cmp x hx => ?_⟩
  have hdm := card_sym2_le cmp.W cmp.card_W
  set W := cmp.W
  -- columnas residuales y realizadores ambientales
  let ι := {T : Finset V // T ∈ allowed H F}
  have hmemL : ∀ T : ι, ind (triEdges T.1) ∈ localGroup H F := fun T =>
    lattice_le_localGroup H F (Submodule.subset_span
      ⟨T.1, (Finset.mem_filter.1 T.2).2, rfl⟩)
  let colT : ι → localGroup H F := fun T => ⟨ind (triEdges T.1), hmemL T⟩
  let B₀ : ι → Fin ((s + 1) ^ 2) → ℤ := fun T => eProj W hdm (cmp.P (colT T))
  let q : ι → Finset V → ℤ := fun T => Pi.single T.1 1 - cmp.C₀ (colT T)
  have hcard3 : ∀ T : ι, (T.1).card = 3 := fun T => (Finset.mem_filter.1 T.2).2.1
  have hB : ∀ T j, |B₀ T j| ≤ (3 * D₀ : ℕ) := by
    intro T j
    refine (abs_eProj_le W hdm _ j).trans ?_
    have := cmp.costP (colT T)
    rw [show (colT T).1 = ind (triEdges T.1) from rfl, l1E_ind_triEdges (hcard3 T)] at this
    push_cast; linarith
  have hq : ∀ T, triBd H F (q T) = eEmb W hdm (B₀ T) := by
    intro T
    simp only [q, B₀, map_sub, triBd_single T.2]
    rw [← cmp.decomp, eEmb_eProj W hdm (cmp.supp _)]
    simp [colT]
  have hJ : ∀ T, ∑ t, |q T t| ≤ (1 + 3 * H₀ : ℕ) := by
    intro T
    have h1 : ∑ t, |q T t| ≤ ∑ t, |(Pi.single T.1 1 : Finset V → ℤ) t| +
        ∑ t, |cmp.C₀ (colT T) t| := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun t _ => abs_sub _ _
    have h2 : ∑ t, |(Pi.single T.1 1 : Finset V → ℤ) t| = 1 := by
      rw [Finset.sum_eq_single T.1]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    have h3 := cmp.costC (colT T)
    rw [show (colT T).1 = ind (triEdges T.1) from rfl, l1E_ind_triEdges (hcard3 T)] at h3
    push_cast; linarith
  -- la demanda
  set x' : localGroup H F := ⟨x, lattice_le_localGroup H F hx⟩
  have hsplit : x - eEmb W hdm (eProj W hdm (cmp.P x')) = triBd H F (cmp.C₀ x') := by
    rw [eEmb_eProj W hdm (cmp.supp _)]; exact cmp.decomp x'
  have hspan : eProj W hdm (cmp.P x') ∈ Submodule.span ℤ (Set.range B₀) := by
    have key : ∀ y (hy : y ∈ lattice H F),
        eProj W hdm (cmp.P ⟨y, lattice_le_localGroup H F hy⟩) ∈
          Submodule.span ℤ (Set.range B₀) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨T, hT, rfl⟩ := hy
        have hTa : T ∈ allowed H F := Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩
        exact Submodule.subset_span ⟨⟨T, hTa⟩, rfl⟩
      | zero =>
        have : (⟨0, lattice_le_localGroup H F (Submodule.zero_mem _)⟩ : localGroup H F) = 0 :=
          rfl
        rw [this, map_zero, map_zero]; exact Submodule.zero_mem _
      | add y z hy hz ihy ihz =>
        have : (⟨y + z, lattice_le_localGroup H F (Submodule.add_mem _ hy hz)⟩ :
            localGroup H F) = ⟨y, lattice_le_localGroup H F hy⟩ +
              ⟨z, lattice_le_localGroup H F hz⟩ := rfl
        rw [this, map_add, map_add]; exact Submodule.add_mem _ ihy ihz
      | smul k y hy ihy =>
        have : (⟨k • y, lattice_le_localGroup H F (Submodule.smul_mem _ k hy)⟩ :
            localGroup H F) = k • ⟨y, lattice_le_localGroup H F hy⟩ := rfl
        rw [this, map_smul, map_smul]; exact Submodule.smul_mem _ k ihy
    exact key x hx
  have hcostC : ∑ t, |cmp.C₀ x' t| ≤ H₀ * ∑ e, |x e| := cmp.costC x'
  have hcostP : IntLift.l1 (eProj W hdm (cmp.P x')) ≤ D₀ * ∑ e, |x e| :=
    (l1_eProj_le W hdm _).trans (cmp.costP x')
  obtain ⟨c, hc, hcc⟩ := hK₀ (triBd H F) (eEmb W hdm) B₀ q H₀ D₀ (1 + 3 * H₀) hB hq hJ
    x (cmp.C₀ x') (eProj W hdm (cmp.P x')) hsplit hcostC hcostP hspan
  refine ⟨c, hc, ?_⟩
  refine hcc.trans (le_of_eq ?_)
  simp only [l1E]; push_cast; ring

/-! ## Conexión con el absorbedor terminal -/

omit [Fintype V] in
lemma l1E_ind [Fintype V] (P : Finset (Sym2 V)) : l1E (ind P) = P.card := by
  simp only [l1E, ind]
  rw [show (∑ e : Sym2 V, |if e ∈ P then (1 : ℤ) else 0|) =
      ∑ e : Sym2 V, if e ∈ P then (1 : ℤ) else 0 from
    Finset.sum_congr rfl fun e _ => by split_ifs <;> simp]
  rw [Finset.sum_boole]; simp [Finset.filter_mem_eq_inter]

/-- **Absorbedor terminal desde un certificado uniforme.** Si `UniformCert H F K` y `P` es
físico con vértices en `Z`, existe un absorbedor de `P` que evita `B`, con
`|A| ≤ K|P| (4C(2h−2,2)+6)`, bajo ventanas expresadas sólo con `|Z|`, `K|P|` y `h`. -/
theorem slot_absorber_of_uniformCert {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) {K : ℕ}
    (hcert : UniformCert H F K)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d) (P : Finset (Sym2 V))
    (hP : IsPhysical H F P) (Z : Finset V) (hPZ : Inside Z P) (Ub : ℕ)
    (hUb : Z.card + 3 * (K * P.card) + K * P.card * (2 * h - 2) +
      3 * (K * P.card) * (2 * h - 3) ≤ Ub)
    (hwin1 : (Ub : ℝ) + 3 + 4 * d < α * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ A, IsAbsorber H F A P ∧ Disjoint A B ∧ A.card ≤ K * P.card * (4 * (2 * h - 2).choose 2 + 6) := by
  obtain ⟨c, hc, hcc⟩ := hcert (ind P) hP
  rw [l1E_ind] at hcc
  set S := allowed H F
  have hS : ∀ T ∈ S, IsAllowed H F T := fun T hT => (Finset.mem_filter.1 hT).2
  have hPc : ∀ e, ind P e = ∑ T ∈ S, c T * ind (triEdges T) e := by
    intro e
    rw [← hc]
    change (∑ T ∈ allowed H F, c T • ind (triEdges T)) e = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hK : ∑ T ∈ S, (c T).natAbs ≤ K * P.card := by
    have h1 : ∑ T ∈ S, |c T| ≤ ∑ T, |c T| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
    have h2 : ((∑ T ∈ S, (c T).natAbs : ℕ) : ℤ) = ∑ T ∈ S, |c T| := by
      simp
    have : ((∑ T ∈ S, (c T).natAbs : ℕ) : ℤ) ≤ ((K * P.card : ℕ) : ℤ) := by
      rw [h2]; push_cast; linarith
    exact_mod_cast this
  -- vértices de los triángulos del soporte
  have hverts : ((S.filter (fun T => c T ≠ 0)).biUnion id).card ≤ 3 * (K * P.card) := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ T ∈ S.filter (fun T => c T ≠ 0), (id T).card
        = ∑ T ∈ S.filter (fun T => c T ≠ 0), 3 :=
          Finset.sum_congr rfl fun T hT => (hS T (Finset.mem_filter.1 hT).1).1
      _ = 3 * (S.filter (fun T => c T ≠ 0)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 3 * ∑ T ∈ S, (c T).natAbs := by
          apply Nat.mul_le_mul_left
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          exact Finset.sum_le_sum fun T _ => by
            split_ifs with h
            · exact Int.natAbs_pos.2 h
            · exact Nat.zero_le _
      _ ≤ 3 * (K * P.card) := Nat.mul_le_mul_left 3 hK
  have hUb' : (Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id).card + (K * P.card) * (2 * h - 2) +
      3 * (K * P.card) * (2 * h - 3) ≤ Ub := by
    have := Finset.card_union_le Z ((S.filter (fun T => c T ≠ 0)).biUnion id)
    omega
  obtain ⟨A, hA, hAB, -, -, hAc⟩ := slot_absorber_of_coeffs hα hH3 hH4 B d hdeg P S hS c hPc
    (K * P.card) hK Z hPZ Ub hUb' hwin1 hwin2
  exact ⟨A, hA, hAB, hAc⟩

end TypedTriangle
