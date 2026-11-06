/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.LocalProfileModule
public import RequestProject.TypedTriangle.ThreeTermAssembly
public import RequestProject.TypedTriangle.PhysicalGrouping

@[expose] public section

/-!
# V16: certificado compuesto del núcleo preparado (V13 → V14 → V15)

1. `physical_blocks_of_cells` (V13 + V14): celdas con signo `b_i ∈ M` (perfiles locales) de
   norma `≤ 3D` con `∑ b_i = x ∈ Λ`, más los DATOS de compresión de V14, dan los bloques
   `y_J = ∑_{i∈J} b_i` con: `y_J ∈ Λ`, `#J ≤ N`, `‖y_J‖₁ ≤ 3DN`, `∑_J y_J = x`,
   `#bloques ≤ I`, y frontera física por bloques `≤` frontera de las celdas originales.
   También exporta las cotas uniformes de rango/torsión del cociente físico `M/(Λ∩M)`.
2. `prepared_core_composed_certificate`: el punto final preparado. LLAMA a
   `routing_budget_real` (V13) para construir las celdas, a `physical_blocks_of_cells`
   (V14) para los bloques físicos, y a `assembled_certificate_V13_frontier` (V15 con la
   frontera de tres términos). No recibe celdas, grupos ni estimaciones de frontera como
   proveedores.

Entradas restantes (interfaces intermedias, no hipótesis de T): las propiedades geométricas
del enrutamiento preparado (las de `routing_budget_real`), `PreparedCore`, `UniformCertOn`
(pendiente del puente local con `uniformCert_of_H3H4`) y los datos finitos de compresión.
Nada de esto es T.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle.Composition

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.ActiveCover
open TypedTriangle.Dispersal TypedTriangle.Grouping TypedTriangle.QuotientBox

universe u v

variable {V : Type u} {I : Type v} [Fintype V] {G : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)}

/-- Generadores de `Λ = SparseEdge.lattice`: indicadores de triángulos permitidos. -/
def latGens (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) : Set (Sym2 V → ℤ) :=
  (fun T => ind (triEdges T)) '' {T | IsAllowed G lab F T}

omit [Fintype V] in
lemma lattice_eq_span : lattice G lab F = Submodule.span ℤ (latGens G lab F) := rfl

/-- **V13 → V14: bloques físicos a partir de las celdas.** Los datos de compresión son los de
V14 (`physical_grouping_of_compression`) sobre `M = localProfile`, `Λ = lattice`:
`x - P x = A (C₀ x)`, `range A ⊆ Λ`, `emb (coord (P x)) = P x`, coordenadas de `P` en los
generadores en `[-R,R]`, y la cota de coordenadas de fichas `‖b‖₁ ≤ 3D ⇒ |coord (P b)| ≤ B`. -/
theorem physical_blocks_of_cells (d R B D : ℕ) {X : Type*} [AddCommGroup X]
    (A : X →ₗ[ℤ] (Sym2 V → ℤ)) (hA : ∀ c, A c ∈ lattice G lab F)
    (C₀ : localProfile G lab F →ₗ[ℤ] X) (P : localProfile G lab F →ₗ[ℤ] (Sym2 V → ℤ))
    (decomp : ∀ x : localProfile G lab F, (x : Sym2 V → ℤ) - P x = A (C₀ x))
    (coord : (Sym2 V → ℤ) →ₗ[ℤ] (Fin d → ℤ)) (emb : (Fin d → ℤ) →ₗ[ℤ] (Sym2 V → ℤ))
    (hrec : ∀ x, emb (coord (P x)) = P x)
    (hbox : ∀ g ∈ latGens G lab F, ∀ hg : g ∈ localProfile G lab F, ∀ k,
      |coord (P ⟨g, hg⟩) k| ≤ R)
    (hcoord : ∀ b : localProfile G lab F, l1E (b : Sym2 V → ℤ) ≤ 3 * D → ∀ k,
      |coord (P b) k| ≤ B)
    (x : Sym2 V → ℤ) (hx : x ∈ lattice G lab F) (cells : List (Sym2 V → ℤ))
    (hM : ∀ b ∈ cells, IsLocalProfile G lab F b)
    (hsum : ∀ e, (cells.map (fun b => b e)).sum = x e)
    (hnorm : ∀ b ∈ cells, norm1 G b ≤ 3 * D) :
    (Module.finrank ℤ (localProfile G lab F ⧸
        (lattice G lab F).comap (localProfile G lab F).subtype) ≤ d ∧
      Nat.card (Submodule.torsion ℤ (localProfile G lab F ⧸
        (lattice G lab F).comap (localProfile G lab F).subtype)) ≤ torBound d R) ∧
    ∃ Q : Finpartition (univ : Finset (Fin cells.length)),
      (∀ J ∈ Q.parts, ∑ i ∈ J, cells.get i ∈ lattice G lab F) ∧
      (∀ J ∈ Q.parts, #J ≤ groupBound d B R) ∧
      (∀ J ∈ Q.parts, l1E (∑ i ∈ J, cells.get i) ≤ 3 * D * groupBound d B R) ∧
      ∑ J ∈ Q.parts, ∑ i ∈ J, cells.get i = x ∧
      Q.parts.card ≤ cells.length ∧
      ∀ v, #(Q.parts.filter fun J => v ∈ front (∑ i ∈ J, cells.get i)) ≤
        cells.countP (fun b => decide (InSupp G v b)) := by
  have hget : ∀ i : Fin cells.length, IsLocalProfile G lab F (cells.get i) :=
    fun i => hM _ (List.get_mem _ _)
  have hl1 : ∀ i : Fin cells.length, l1E (cells.get i) ≤ 3 * D := fun i => by
    rw [l1E_eq_norm1 (hget i).1]; exact hnorm _ (List.get_mem _ _)
  let b : Fin cells.length → localProfile G lab F := fun i => ⟨cells.get i, hget i⟩
  have hsumx : ∑ i, cells.get i = x := by
    funext e
    rw [Finset.sum_apply, sum_get_eq cells (fun b => b e)]
    exact hsum e
  obtain ⟨hquot, Q, hQ⟩ := physical_grouping_of_compression d B R (localProfile G lab F)
    (lattice G lab F) (latGens G lab F) lattice_eq_span (lattice_le_localProfile G lab F)
    A hA C₀ P decomp coord emb hrec hbox b (fun i k => hcoord (b i) (hl1 i) k)
    (by show ∑ i, cells.get i ∈ _; rw [hsumx]; exact hx)
  refine ⟨hquot, Q, fun J hJ => (hQ J hJ).2, fun J hJ => (hQ J hJ).1, fun J hJ => ?_, ?_, ?_,
    fun v => ?_⟩
  · have h1 := normOn_blockSum_le_card_mul (fun i => cells.get i) univ J (3 * D)
      (fun i _ => hl1 i)
    have h2 : (#J : ℤ) ≤ groupBound d B R := by exact_mod_cast (hQ J hJ).1
    have h3 : (#J : ℤ) * (3 * D) ≤ groupBound d B R * (3 * D) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have : l1E (∑ i ∈ J, cells.get i) = normOn univ (∑ i ∈ J, cells.get i) := rfl
    linarith
  · have hbu := Finset.sum_biUnion (s := Q.parts) (t := id) (f := fun i => cells.get i)
      Q.disjoint
    simp only [id] at hbu
    rw [← hbu, Q.biUnion_parts]
    exact hsumx
  · have := Q.card_parts_le_card
    simpa using this
  · refine (card_blocks_front_le (fun i => cells.get i) (fun i => (hget i).1) Q.parts
      Q.disjoint v).trans (le_of_eq ?_)
    exact card_filter_get_eq_countP cells (fun b => InSupp G v b)

lemma card_univ_filter_subtype {ι : Type*} (P : Finset (Finset ι)) (φ : Finset ι → Prop)
    [DecidablePred φ] :
    (univ.filter (fun J : {J // J ∈ P} => φ J.1)).card = (P.filter φ).card := by
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext J; simp [and_comm]

/-- **Certificado compuesto del núcleo preparado (V13 → V14 → V15).**

Constantes fijadas ANTES del host: `D, C, δ` (enrutamiento), `d, R, B` (compresión),
`N = groupBound d B R`, `k = 3DN`, y `K` el de `UniformCertOn` en `k`; `β` del núcleo
preparado. Para todo host con las propiedades preparadas y todo `x ∈ Λ`, existe un
certificado con signo de borde EXACTO `x`, norma `≤ 2K‖x‖₁` y congestión
`≤ K((4D+3)·d_abs(x)(v) + (32D/δ + 12K/β)·‖x‖₁/n + 2D + 2)`.

Las celdas (V13, `routing_budget_real`), los bloques físicos (V14,
`physical_blocks_of_cells`) y las cotas de frontera se CONSTRUYEN aquí. El caso `x = 0`
(`‖x‖₁ = 0`) usa el certificado nulo. -/
theorem prepared_core_composed_certificate
    {α : ℝ} {h N₀ K : ℕ} {β : ℝ} {C D : ℕ} (δ : ℝ) (d R B : ℕ)
    (hU : UniformCertOn.{u} F α h N₀ (3 * D * groupBound d B R) K)
    (Pc : PreparedCore G lab F α h N₀ β) (hβ : 0 < β)
    -- propiedades geométricas del enrutamiento preparado (entradas de `routing_budget_real`)
    (hδ : 0 < δ) (hδC : C * δ ≤ 4) (hn : 0 < Fintype.card V)
    (hrows : ∀ v, (univ.filter (fun j : Row V => j.1 = v ∧ IsActiveRow G lab F j)).card ≤ C)
    (hdeg : ∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ C * j.2.card)
    (hdel : ∀ A : Finset V, (A.card : ℝ) ≤ δ * Fintype.card V → DeletionHyp G lab F A)
    (hD1 : 1 ≤ D) (hD : 12 * C ^ 2 ≤ D + 1)
    -- datos finitos de compresión de V14 sobre `M = localProfile`, `Λ = lattice`
    {X : Type*} [AddCommGroup X]
    (A : X →ₗ[ℤ] (Sym2 V → ℤ)) (hA : ∀ c, A c ∈ lattice G lab F)
    (C₀ : localProfile G lab F →ₗ[ℤ] X) (P : localProfile G lab F →ₗ[ℤ] (Sym2 V → ℤ))
    (decomp : ∀ x : localProfile G lab F, (x : Sym2 V → ℤ) - P x = A (C₀ x))
    (coord : (Sym2 V → ℤ) →ₗ[ℤ] (Fin d → ℤ)) (emb : (Fin d → ℤ) →ₗ[ℤ] (Sym2 V → ℤ))
    (hrec : ∀ x, emb (coord (P x)) = P x)
    (hbox : ∀ g ∈ latGens G lab F, ∀ hg : g ∈ localProfile G lab F, ∀ k,
      |coord (P ⟨g, hg⟩) k| ≤ R)
    (hcoord : ∀ b : localProfile G lab F, l1E (b : Sym2 V → ℤ) ≤ 3 * D → ∀ k,
      |coord (P b) k| ≤ B)
    (x : Sym2 V → ℤ) (hx : x ∈ lattice G lab F) :
    ∃ cert : Finset V → ℤ, IsCert G lab F cert x ∧
      (l1T cert : ℝ) ≤ 2 * K * norm1 G x ∧
      ∀ v, (vload cert v : ℝ) ≤
        K * ((4 * D + 3) * dabs G x v +
          (32 * D / δ + 12 * K / β) * (norm1 G x / Fintype.card V) + 2 * D + 2) := by
  have hxE : EdgeSupp G x := edgeSupp_of_lattice hx
  have hle : l1E x = norm1 G x := l1E_eq_norm1 hxE
  rcases (norm1_nonneg (G := G) x).lt_or_eq with he | he
  · -- V13: celdas construidas por `routing_budget_real`
    obtain ⟨cells, hM, hsum, hlen, hnorm, -, hfront⟩ :=
      routing_budget_real x (lattice_le_localProfile G lab F hx) δ hδ hδC he hn hrows hdeg
        hdel hD1 hD
    -- V14: bloques físicos
    obtain ⟨-, Q, hQΛ, -, hQk, hQsum, hQcard, hQfront⟩ :=
      physical_blocks_of_cells d R B D A hA C₀ P decomp coord emb hrec hbox hcoord x hx cells
        hM hsum hnorm
    let y : Q.parts → Sym2 V → ℤ := fun J => ∑ i ∈ J.1, cells.get i
    have hdec : ∑ J, y J = x := by
      rw [← hQsum]
      exact Finset.sum_coe_sort Q.parts (fun J => ∑ i ∈ J, cells.get i)
    have hJ : (Fintype.card Q.parts : ℤ) ≤ 2 * l1E x := by
      rw [Fintype.card_coe, hle]
      have : (Q.parts.card : ℤ) ≤ cells.length := by exact_mod_cast hQcard
      linarith
    have hF : ∀ v, ((univ.filter (fun J => v ∈ front (y J))).card : ℤ) ≤
        (4 * D + 3) * dabs G x v +
          ⌈32 * D * (l1E x : ℝ) / (δ * Fintype.card V)⌉₊ + 2 * D := by
      intro v
      have h1 := card_univ_filter_subtype Q.parts (fun J => v ∈ front (∑ i ∈ J, cells.get i))
      have h2 : ((univ.filter (fun J => v ∈ front (y J))).card : ℤ) ≤
          cells.countP (fun b => decide (InSupp G v b)) := by
        exact_mod_cast h1.trans_le (hQfront v)
      have h3 := hfront v
      have h4 := dabs_nonneg (G := G) x v
      have hD0 : (0 : ℤ) ≤ D := by positivity
      rw [hle]
      nlinarith
    obtain ⟨cert, hcert, hl1, hload⟩ := assembled_certificate_V13_frontier hU Pc hβ hn x y hdec
      (fun J => hQΛ J.1 J.2) (fun J => hQk J.1 J.2) hJ D δ hδ (dabs G x) hF
    rw [hle] at hl1 hload
    exact ⟨cert, hcert, hl1, hload⟩
  · -- `‖x‖₁ = 0`: `x = 0` y el certificado nulo
    have hx0 : x = 0 := eq_zero_of_norm1_eq_zero hxE he.symm
    refine ⟨0, ⟨fun T hT => absurd rfl hT, ?_⟩, ?_, fun v => ?_⟩
    · rw [hx0]; funext e; simp [triBd]
    · simp [l1T, ← he]
    · have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
      have hd := dabs_nonneg (G := G) x v
      have hdR : (0 : ℝ) ≤ dabs G x v := by exact_mod_cast hd
      have : (vload (0 : Finset V → ℤ) v : ℝ) = 0 := by simp [vload]
      rw [this, ← he]
      push_cast
      positivity

/-- **Forma con constante común**: `K' = K(4D+3 + 32D/δ + 12K/β + 2D + 2)`, independiente de
`n` y `x`: norma `≤ K'‖x‖₁` y congestión `≤ K'(d_abs(x)(v) + ‖x‖₁/n + 1)`. -/
theorem prepared_core_composed_certificate_uniform
    {α : ℝ} {h N₀ K : ℕ} {β : ℝ} {C D : ℕ} (δ : ℝ) (d R B : ℕ)
    (hU : UniformCertOn.{u} F α h N₀ (3 * D * groupBound d B R) K)
    (Pc : PreparedCore G lab F α h N₀ β) (hβ : 0 < β)
    (hδ : 0 < δ) (hδC : C * δ ≤ 4) (hn : 0 < Fintype.card V)
    (hrows : ∀ v, (univ.filter (fun j : Row V => j.1 = v ∧ IsActiveRow G lab F j)).card ≤ C)
    (hdeg : ∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ C * j.2.card)
    (hdel : ∀ A : Finset V, (A.card : ℝ) ≤ δ * Fintype.card V → DeletionHyp G lab F A)
    (hD1 : 1 ≤ D) (hD : 12 * C ^ 2 ≤ D + 1)
    {X : Type*} [AddCommGroup X]
    (A : X →ₗ[ℤ] (Sym2 V → ℤ)) (hA : ∀ c, A c ∈ lattice G lab F)
    (C₀ : localProfile G lab F →ₗ[ℤ] X) (P : localProfile G lab F →ₗ[ℤ] (Sym2 V → ℤ))
    (decomp : ∀ x : localProfile G lab F, (x : Sym2 V → ℤ) - P x = A (C₀ x))
    (coord : (Sym2 V → ℤ) →ₗ[ℤ] (Fin d → ℤ)) (emb : (Fin d → ℤ) →ₗ[ℤ] (Sym2 V → ℤ))
    (hrec : ∀ x, emb (coord (P x)) = P x)
    (hbox : ∀ g ∈ latGens G lab F, ∀ hg : g ∈ localProfile G lab F, ∀ k,
      |coord (P ⟨g, hg⟩) k| ≤ R)
    (hcoord : ∀ b : localProfile G lab F, l1E (b : Sym2 V → ℤ) ≤ 3 * D → ∀ k,
      |coord (P b) k| ≤ B)
    (x : Sym2 V → ℤ) (hx : x ∈ lattice G lab F) :
    ∃ cert : Finset V → ℤ, IsCert G lab F cert x ∧
      (l1T cert : ℝ) ≤ K * (4 * D + 3 + 32 * D / δ + 12 * K / β + 2 * D + 2) * norm1 G x ∧
      ∀ v, (vload cert v : ℝ) ≤
        K * (4 * D + 3 + 32 * D / δ + 12 * K / β + 2 * D + 2) *
          (dabs G x v + norm1 G x / Fintype.card V + 1) := by
  obtain ⟨cert, hcert, hl1, hload⟩ := prepared_core_composed_certificate δ d R B hU Pc hβ hδ
    hδC hn hrows hdeg hdel hD1 hD A hA C₀ P decomp coord emb hrec hbox hcoord x hx
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hx0 : (0 : ℝ) ≤ norm1 G x := by exact_mod_cast norm1_nonneg (G := G) x
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have p1 : (0 : ℝ) ≤ 32 * D / δ := by positivity
  have p2 : (0 : ℝ) ≤ 12 * K / β := by positivity
  have hxn : (0 : ℝ) ≤ norm1 G x / Fintype.card V := by positivity
  set S : ℝ := 4 * D + 3 + 32 * D / δ + 12 * K / β + 2 * D + 2
  refine ⟨cert, hcert, hl1.trans ?_, fun v => (hload v).trans ?_⟩
  · have : (2 : ℝ) * K ≤ K * S := by
      have : (2 : ℝ) ≤ S := by simp only [S]; linarith
      nlinarith
    exact mul_le_mul_of_nonneg_right this hx0
  · have hdv : (0 : ℝ) ≤ dabs G x v := by exact_mod_cast dabs_nonneg (G := G) x v
    have key : (4 * D + 3) * (dabs G x v : ℝ) +
        (32 * D / δ + 12 * K / β) * (norm1 G x / Fintype.card V) + 2 * D + 2 ≤
        S * (dabs G x v + norm1 G x / Fintype.card V + 1) := by
      have e1 : (4 * D + 3) * (dabs G x v : ℝ) ≤ S * dabs G x v :=
        mul_le_mul_of_nonneg_right (by simp only [S]; linarith) hdv
      have e2 : (32 * D / δ + 12 * K / β) * (norm1 G x / Fintype.card V) ≤
          S * (norm1 G x / Fintype.card V) :=
        mul_le_mul_of_nonneg_right (by simp only [S]; linarith) hxn
      have e3 : (2 * D + 2 : ℝ) ≤ S := by simp only [S]; linarith
      nlinarith
    calc _ ≤ (K : ℝ) * (S * (dabs G x v + norm1 G x / Fintype.card V + 1)) :=
          mul_le_mul_of_nonneg_left key hK0
      _ = _ := by ring

end TypedTriangle.Composition
