/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SampleAverage

@[expose] public section

/-!
# G1-Z, §§6–7 de la guía V6 — Construcción de `W`, `Z`, `d`

Sobre la MISMA muestra firmada `y = (x, s)`:

* `card_badRoot_le`: para cada raíz `v`, la fracción de muestras para las que `v` es mala es
  `≤ (1/α)·2ε` (unión sobre las `≤ 1/α` componentes activas del enlace, base y doble cubierta);
* `exists_sample`: existe una muestra con pocas raíces malas y pocos vértices de grado alto en
  `B(W)`;
* `exists_WZd`: construcción concreta de `W, Z, d` que paga todas las ventanas de
  `uniformCert_of_goodRoots`.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence Sampler

lemma minDegOn_mono {Ω : Type*} [Fintype Ω] {J : SimpleGraph Ω} {K : Finset Ω} {c c' : ℝ}
    (h : MinDegOn J K c) (hle : c' ≤ c) : MinDegOn J K c' := by
  intro x hx
  have := h x hx
  have : (0 : ℝ) ≤ Fintype.card Ω := by positivity
  nlinarith

lemma robustConn_mono {Ω : Type*} [Fintype Ω] {J : SimpleGraph Ω} {K : Finset Ω}
    {ζ ρ ζ' ρ' : ℝ} (h : RobustConn J K ζ ρ) (hζ : ζ' ≤ ζ) (hρ : ρ' ≤ ρ) :
    RobustConn J K ζ' ρ' := by
  intro Z B hZ hB
  have hN : (0 : ℝ) ≤ Fintype.card Ω := by positivity
  exact h Z B (hZ.trans (by nlinarith)) (fun x => (hB x).trans (by nlinarith))

/-- Ventanas aritméticas comunes. -/
lemma windows_of {α θ n z d P2 hh : ℝ} (hθ : 0 ≤ θ) (hP2 : 1 ≤ P2)
    (hθP : θ * 64 * P2 ≤ α) (hn : 0 ≤ n) (hn1 : 4 ≤ α * n) (hn2 : 4 * hh * P2 ≤ α * n)
    (hz0 : 0 ≤ z) (hz : z ≤ θ * n) (hd : d ≤ θ * n) :
    z + 2 + 4 * d < α * n ∧ (z + hh + 5 * d) * P2 ≤ α / 2 * n ∧ z + d ≤ α * n / 2 := by
  have hθα : θ * 64 ≤ α := by nlinarith
  have h1 : θ * n * 64 ≤ α * n := by nlinarith
  have h2 : θ * n * P2 * 64 ≤ α * n := by nlinarith
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  have : z * P2 + 5 * d * P2 ≤ 6 * (θ * n * P2) := by nlinarith
  nlinarith

lemma card_of_fst {α β : Type*} [Fintype α] [Fintype β] (P : α → Prop) [DecidablePred P] (s : Finset (α × β))
    (hs : ∀ x, x ∈ s ↔ P x.1) : s.card = (univ.filter P).card * Fintype.card β := by
  rw [show s = (univ.filter P) ×ˢ univ by ext x; simp [hs], Finset.card_product,
    Finset.card_univ]

lemma card_le_of_equiv {α β : Type*} (e : α ≃ β) (s : Finset α) (t : Finset β)
    (h : ∀ a ∈ s, e a ∈ t) : s.card ≤ t.card :=
  Finset.card_le_card_of_injOn e (fun a ha => h a ha) (fun _ _ _ _ hab => e.injective hab)

variable {V I : Type} [Fintype V]

/-- **Fallo por raíz.** Para una raíz `v`, las muestras firmadas para las que `v` es mala son
a lo sumo `|comps|·2ε` de todas. -/
theorem card_badRoot_le {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) {θ κ ε : ℝ}
    (hθ : 0 < θ) (hε : 0 ≤ ε) (hθα : θ ≤ α) (hκ : κ = expConst (α / 2) (θ / 2) (θ / 4))
    (hw1 : θ * Fintype.card V + 2 + 4 * (θ * Fintype.card V) < α * Fintype.card V)
    (hw2 : (θ * Fintype.card V + h + 5 * (θ * Fintype.card V)) * 2 ^ Nat.choose h 2 ≤
      α / 2 * Fintype.card V)
    {L Q b : ℕ}
    (hcs : ∀ {Ω : Type} [Fintype Ω] (J : SimpleGraph Ω) (K : Finset Ω),
      K.Nonempty → NbrClosed J K → MinDegOn J K (α / 2) → ExpandOn J K (α / 2) κ →
      ∀ M : (Fin L → Fin Q → Ω) → Finset Ω, (∀ p, (M p).card ≤ 1) →
      ((univ.filter (fun x : (Fin L → Fin Q → Ω) × (Fin b → Ω) =>
        ¬ SampleGood J K (M x.1) (pvals x.1) (pvals x.1 ∪ fvals x.2))).card : ℝ) ≤
        ε * Fintype.card ((Fin L → Fin Q → Ω) × (Fin b → Ω)))
    (v : V) :
    ((univ.filter (fun y : XS L Q b V × XS L Q b Bool => BadRoot H F v y)).card : ℝ) ≤
      (comps H F v).card * (2 * ε * Fintype.card (XS L Q b V × XS L Q b Bool)) := by
  set G := linkGraph H F v
  set Y := XS L Q b V × XS L Q b Bool
  have hθ2 : θ / 2 ≤ α / 2 := by linarith
  -- fallo base por componente
  have hbase : ∀ K ∈ comps H F v,
      ((univ.filter (fun y : Y => ¬ SampleGood G K ∅ (pvals y.1.1) (baseW y.1))).card : ℝ) ≤
        ε * Fintype.card Y := by
    intro K hK
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hK
    have hact : Active G a := (Finset.mem_filter.1 ha).2
    have hrob : RobustConn G (compOf G a) (θ / 2) (θ / 4) :=
      link_robustConn hα hH3 hH4 v a (by positivity)
        (by nlinarith [(by positivity : (0 : ℝ) ≤ Fintype.card V)])
        (by
          refine le_trans ?_ hw2
          have : (0 : ℝ) ≤ Fintype.card V := by positivity
          gcongr <;> nlinarith)
    have hexp : ExpandOn G (compOf G a) (α / 2) κ := by
      rw [hκ]
      exact expandOn_of_robust (by positivity) (by positivity) hθ2 (by positivity)
        (compOf_closed G a) (minDegOn_mono (link_minDegOn hH3 hact) (by linarith)) hrob
    have h1 := hcs G (compOf G a) ⟨a, mem_compOf.2 (SimpleGraph.Reachable.refl a)⟩
      (compOf_closed G a) (minDegOn_mono (link_minDegOn hH3 hact) (by linarith)) hexp
      (fun _ => ∅) (fun _ => by simp)
    have e2 : (univ.filter (fun y : Y =>
        ¬ SampleGood G (compOf G a) ∅ (pvals y.1.1) (baseW y.1))).card =
        (univ.filter (fun x : XS L Q b V =>
          ¬ SampleGood G (compOf G a) ∅ (pvals x.1) (pvals x.1 ∪ fvals x.2))).card *
          Fintype.card (XS L Q b Bool) :=
      card_of_fst (fun x : XS L Q b V =>
        ¬ SampleGood G (compOf G a) ∅ (pvals x.1) (pvals x.1 ∪ fvals x.2))
        (univ.filter (fun y : Y =>
          ¬ SampleGood G (compOf G a) ∅ (pvals y.1.1) (baseW y.1))) fun y => by
        constructor
        · intro hy
          exact (Finset.mem_filter.mp hy).2
        · intro hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    have h1' : ((univ.filter (fun x : XS L Q b V =>
          ¬ SampleGood G (compOf G a) ∅ (pvals x.1) (pvals x.1 ∪ fvals x.2))).card : ℝ) ≤
        ε * Fintype.card (XS L Q b V) := by
      simpa only [XS] using h1
    rw [e2, show Fintype.card Y = Fintype.card (XS L Q b V) * Fintype.card (XS L Q b Bool) from
      Fintype.card_prod _ _]
    push_cast
    calc _ ≤ ε * Fintype.card (XS L Q b V) * Fintype.card (XS L Q b Bool) :=
          mul_le_mul_of_nonneg_right h1' (by positivity)
      _ = _ := by ring
  -- fallo de la doble cubierta por componente
  have hcov : ∀ K ∈ comps H F v,
      ((univ.filter (fun y : Y => (∀ a ∈ K, OddAt G a) ∧
        ¬ SampleGood (dcover G) (K ×ˢ (univ : Finset Bool))
          (markC (K ×ˢ (univ : Finset Bool)) (zipS y.1 y.2).1) (pvals (zipS y.1 y.2).1)
          (baseW (zipS y.1 y.2)))).card : ℝ) ≤ ε * Fintype.card Y := by
    intro K hK
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hK
    have hact : Active G a := (Finset.mem_filter.1 ha).2
    by_cases hodd : ∀ x ∈ compOf G a, OddAt G x
    · set Kt := compOf G a ×ˢ (univ : Finset Bool)
      have hrob : RobustConn (dcover G) Kt (θ / 2) (θ / 4) :=
        cover_robustConn hα hH3 hH4 v (compOf_closed G a) (fun _ hx _ hy => compOf_reach hx hy)
          hodd hθ.le hw1 hw2
      have hmd : MinDegOn (dcover G) Kt (α / 2) :=
        dcover_minDegOn hH3 (fun x hx => active_of_mem_compOf hact hx)
      have hcl : NbrClosed (dcover G) Kt := dcover_closed G (compOf_closed G a)
      have hexp : ExpandOn (dcover G) Kt (α / 2) κ := by
        rw [hκ]
        exact expandOn_of_robust (by positivity) (by positivity) hθ2 (by positivity) hcl hmd hrob
      have h2 := hcs (dcover G) Kt
        ⟨(a, false), Finset.mem_product.2 ⟨mem_compOf.2 (SimpleGraph.Reachable.refl a),
          Finset.mem_univ _⟩⟩ hcl hmd hexp (markC Kt) (card_markC_le Kt)
      have hcard : Fintype.card Y = Fintype.card (XS L Q b (V × Bool)) :=
        Fintype.card_congr (zipE L Q b V Bool)
      rw [hcard]
      refine le_trans (Nat.cast_le.2 (card_le_of_equiv (zipE L Q b V Bool) _ _ (fun y hy => ?_)))
        h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      convert hy.2 using 2 <;>
        first | rfl | (unfold baseW; congr; exact Subsingleton.elim _ _)
    · have : univ.filter (fun y : Y => (∀ x ∈ compOf G a, OddAt G x) ∧
          ¬ SampleGood (dcover G) (compOf G a ×ˢ (univ : Finset Bool))
            (markC (compOf G a ×ˢ (univ : Finset Bool)) (zipS y.1 y.2).1)
            (pvals (zipS y.1 y.2).1) (baseW (zipS y.1 y.2))) = ∅ := by
        ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        exact fun h => absurd h hodd
      rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  -- unión sobre las componentes
  have hsub : univ.filter (fun y : Y => BadRoot H F v y) ⊆ (comps H F v).biUnion (fun K =>
      univ.filter (fun y : Y => ¬ SampleGood G K ∅ (pvals y.1.1) (baseW y.1)) ∪
      univ.filter (fun y : Y => (∀ a ∈ K, OddAt G a) ∧
        ¬ SampleGood (dcover G) (K ×ˢ (univ : Finset Bool))
          (markC (K ×ˢ (univ : Finset Bool)) (zipS y.1 y.2).1) (pvals (zipS y.1 y.2).1)
          (baseW (zipS y.1 y.2)))) := by
    intro y hy
    obtain ⟨K, hK, hb⟩ := (Finset.mem_filter.1 hy).2
    refine Finset.mem_biUnion.2 ⟨K, hK, ?_⟩
    rcases hb with hb | hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)
  calc ((univ.filter (fun y : Y => BadRoot H F v y)).card : ℝ)
      ≤ (((comps H F v).biUnion (fun K =>
      univ.filter (fun y : Y => ¬ SampleGood G K ∅ (pvals y.1.1) (baseW y.1)) ∪
      univ.filter (fun y : Y => (∀ a ∈ K, OddAt G a) ∧
        ¬ SampleGood (dcover G) (K ×ˢ (univ : Finset Bool))
          (markC (K ×ˢ (univ : Finset Bool)) (zipS y.1 y.2).1) (pvals (zipS y.1 y.2).1)
          (baseW (zipS y.1 y.2))))).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ K ∈ comps H F v, (((univ.filter (fun y : Y =>
          ¬ SampleGood G K ∅ (pvals y.1.1) (baseW y.1))).card : ℝ) +
        ((univ.filter (fun y : Y => (∀ a ∈ K, OddAt G a) ∧
        ¬ SampleGood (dcover G) (K ×ˢ (univ : Finset Bool))
          (markC (K ×ˢ (univ : Finset Bool)) (zipS y.1 y.2).1) (pvals (zipS y.1 y.2).1)
          (baseW (zipS y.1 y.2)))).card : ℝ)) := by
        refine (Nat.cast_le.2 Finset.card_biUnion_le).trans ?_
        push_cast
        exact Finset.sum_le_sum fun K _ => by exact_mod_cast Finset.card_union_le _ _
    _ ≤ ∑ _K ∈ comps H F v, (2 * ε * Fintype.card Y) :=
        Finset.sum_le_sum fun K hK => by linarith [hbase K hK, hcov K hK]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

lemma sum_card_filter_comm {A B : Type*} [Fintype A] [Fintype B] (R : A → B → Prop) :
    ∑ a : A, (univ.filter (fun b => R a b)).card = ∑ b : B, (univ.filter (fun a => R a b)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

lemma card_sym2_le_sq : Fintype.card (Sym2 V) ≤ Fintype.card V * Fintype.card V := by
  rw [← Fintype.card_prod]
  exact Fintype.card_le_of_surjective _ Sym2.mk_surjective

/-- **Muestra común buena.** Existe una muestra firmada con pocas raíces malas y pocos vértices
de grado alto en `B(W)`, ambos sobre la MISMA muestra. -/
theorem exists_sample {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) {θ κ : ℝ}
    (hα1 : α ≤ 1) (hθ : 0 < θ) (hθα : θ ≤ α) (hκ : κ = expConst (α / 2) (θ / 2) (θ / 4))
    (hn : 0 < Fintype.card V)
    (hw1 : θ * Fintype.card V + 2 + 4 * (θ * Fintype.card V) < α * Fintype.card V)
    (hw2 : (θ * Fintype.card V + h + 5 * (θ * Fintype.card V)) * 2 ^ Nat.choose h 2 ≤
      α / 2 * Fintype.card V)
    {L Q b : ℕ} (hL : 1 ≤ L) (hQ : (1 - α) ^ Q ≤ θ ^ 2 / 16)
    (hcs : ∀ {Ω : Type} [Fintype Ω] (J : SimpleGraph Ω) (K : Finset Ω),
      K.Nonempty → NbrClosed J K → MinDegOn J K (α / 2) → ExpandOn J K (α / 2) κ →
      ∀ M : (Fin L → Fin Q → Ω) → Finset Ω, (∀ p, (M p).card ≤ 1) →
      ((univ.filter (fun x : (Fin L → Fin Q → Ω) × (Fin b → Ω) =>
        ¬ SampleGood J K (M x.1) (pvals x.1) (pvals x.1 ∪ fvals x.2))).card : ℝ) ≤
        α * θ / 16 * Fintype.card ((Fin L → Fin Q → Ω) × (Fin b → Ω))) :
    ∃ y : XS L Q b V × XS L Q b Bool,
      ((univ.filter (fun v => BadRoot H F v y)).card : ℝ) +
        (univ.filter (fun x => ⌊θ * Fintype.card V⌋₊ <
          degIn (noThird H F (baseW y.1)) x)).card ≤ θ * Fintype.card V / 4 := by
  set Y := XS L Q b V × XS L Q b Bool
  set n : ℝ := (Fintype.card V : ℝ)
  have hnpos : 0 < n := Nat.cast_pos.2 hn
  set D := ⌊θ * n⌋₊
  have hNY : 0 < Fintype.card Y := by
    have : Nonempty V := Fintype.card_pos_iff.1 hn
    exact Fintype.card_pos
  have hYpos : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hNY
  -- raíces malas
  have hbad_v : ∀ v : V, ((univ.filter (fun y : Y => BadRoot H F v y)).card : ℝ) ≤
      θ / 8 * Fintype.card Y := by
    intro v
    have h1 := card_badRoot_le hα hH3 hH4 hθ (by positivity) hθα hκ hw1 hw2 hcs v
    have h2 := card_comps_le hH3 v
    have h3 : ((comps H F v).card : ℝ) * α ≤ 1 := by
      have : ((comps H F v).card : ℝ) * α * n ≤ 1 * n := by nlinarith
      exact le_of_mul_le_mul_right this hnpos
    refine h1.trans ?_
    have : (0 : ℝ) ≤ Fintype.card Y := hYpos.le
    have e : ((comps H F v).card : ℝ) * (2 * (α * θ / 16) * Fintype.card Y) =
        ((comps H F v).card * α) * (θ / 8 * Fintype.card Y) := by ring
    rw [e]
    have : 0 ≤ θ / 8 * Fintype.card Y := by positivity
    nlinarith
  have hbad : (∑ y : Y, ((univ.filter (fun v => BadRoot H F v y)).card : ℝ)) ≤
      n * (θ / 8 * Fintype.card Y) := by
    have e' : (∑ y : Y, ((univ.filter (fun v => BadRoot H F v y)).card : ℝ)) =
        ∑ v : V, ((univ.filter (fun y : Y => BadRoot H F v y)).card : ℝ) := by
      simp only [Finset.card_filter]; push_cast; exact Finset.sum_comm
    rw [e']
    calc _ ≤ ∑ _v : V, θ / 8 * (Fintype.card Y : ℝ) := Finset.sum_le_sum fun v _ => hbad_v v
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- grado alto
  have hhigh0 := sum_highDeg_le_gen hH3 (Y := Y) (fun y => baseW y.1)
    (θ := (1 - α) ^ Q) (pow_nonneg (by linarith) _)
    (fun A hA => card_avoid_le hL A hA) D
  have hD1 : θ * n < D + 1 := Nat.lt_floor_add_one _
  have hsym : (Fintype.card (Sym2 V) : ℝ) ≤ n * n := by
    show (Fintype.card (Sym2 V) : ℝ) ≤ (Fintype.card V : ℝ) * Fintype.card V
    exact_mod_cast card_sym2_le_sq
  set S := ∑ y : Y, ((univ.filter (fun x => D < degIn (noThird H F (baseW y.1)) x)).card : ℝ)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hhigh : S ≤ n * (θ / 8 * Fintype.card Y) := by
    have hpow0 : 0 ≤ (1 - α) ^ Q := pow_nonneg (by linarith) _
    have h1 : S * (θ * n) ≤ 2 * (n * n) * (θ ^ 2 / 16 * Fintype.card Y) := by
      calc S * (θ * n) ≤ S * (D + 1) := mul_le_mul_of_nonneg_left hD1.le hS0
        _ ≤ 2 * Fintype.card (Sym2 V) * ((1 - α) ^ Q * Fintype.card Y) := hhigh0
        _ ≤ 2 * (n * n) * (θ ^ 2 / 16 * Fintype.card Y) := by gcongr
    have h2 : 2 * (n * n) * (θ ^ 2 / 16 * Fintype.card Y) =
        (n * (θ / 8 * Fintype.card Y)) * (θ * n) := by ring
    rw [h2] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  -- promedio
  have htot : ∑ y : Y, (((univ.filter (fun v => BadRoot H F v y)).card : ℝ) +
      (univ.filter (fun x => D < degIn (noThird H F (baseW y.1)) x)).card) ≤
      ∑ _y : Y, θ * n / 4 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : n * (θ / 8 * Fintype.card Y) + n * (θ / 8 * Fintype.card Y) =
        (Fintype.card Y : ℝ) * (θ * n / 4) := by ring
    linarith
  obtain ⟨y, -, hy⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty_iff.2 (Fintype.card_pos_iff.1 hNY)) htot
  exact ⟨y, hy⟩

omit [Fintype V] in
lemma degIn_mono {B B' : Finset (Sym2 V)} (h : B ⊆ B') (x : V) : degIn B x ≤ degIn B' x :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- **Constructor de `W, Z, d` y certificado uniforme desde H3–H4.** Para `α > 0` y `h`
fijos existen `K` y `n₀` tales que todo host de orden `n ≥ n₀` que satisface H3 y H4 con
constante `α` admite el certificado uniforme `UniformCert H F K`. La muestra `W`, el conjunto
excepcional `Z` y la cota de grado `d` se construyen sobre UNA misma muestra firmada; `α` se
clampa a `min α 1` por monotonía de H3/H4. No se añaden hipótesis de densidad, tipicidad ni
raíces buenas. -/
theorem uniformCert_of_H3H4 (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ K n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
      n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h → UniformCert H F K := by
  set a := min α 1 with ha_def
  have ha0 : 0 < a := lt_min hα one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  have haα : a ≤ α := min_le_left _ _
  set P2 : ℝ := (2 : ℝ) ^ Nat.choose h 2
  have hP2 : 1 ≤ P2 := one_le_pow₀ (by norm_num)
  set θ := a / (64 * P2)
  have hθ : 0 < θ := by positivity
  have hθP : θ * 64 * P2 = a := by
    simp only [θ]; field_simp
  have hθa : θ ≤ a := by nlinarith
  set κ := expConst (a / 2) (θ / 2) (θ / 4)
  have hκ0 : 0 < κ := expConst_pos (by positivity) (by positivity) (by positivity)
  have hκ1 : κ ≤ 1 := expConst_le_one (by linarith)
  obtain ⟨m0, hm0⟩ := exists_pow_lt_of_lt_one (x := θ ^ 2 / 16) (y := 1 - a) (by positivity)
    (by linarith)
  obtain ⟨L, Q, b, hL, hQ, hcs⟩ := component_sample.{0} (c := a / 2) (κ := κ)
    (ε := a * θ / 16) 1 m0 (by positivity) (by linarith) hκ0 hκ1 (by positivity)
  obtain ⟨K, hK⟩ := uniformCert_of_goodRoots a (L * Q + b)
  refine ⟨K, ⌈4 / a⌉₊ + ⌈4 * h * P2 / a⌉₊ + 1, fun {V I} _ H F hn hH3 hH4 => ?_⟩
  have hH3' := commonNbrCond_mono hH3 haα
  have hH4' := hingeCond_mono hH4 haα
  set n : ℝ := (Fintype.card V : ℝ)
  have hnN : 0 < Fintype.card V := by omega
  have hnpos : 0 < n := Nat.cast_pos.2 hnN
  have hn1 : 4 ≤ a * n := by
    have h1 : (⌈4 / a⌉₊ : ℝ) ≤ n := by
      show (⌈4 / a⌉₊ : ℝ) ≤ (Fintype.card V : ℝ)
      exact_mod_cast (by omega : ⌈4 / a⌉₊ ≤ Fintype.card V)
    have h2 := (Nat.le_ceil (4 / a)).trans h1
    rw [div_le_iff₀ ha0] at h2; linarith
  have hn2 : 4 * h * P2 ≤ a * n := by
    have h1 : (⌈4 * h * P2 / a⌉₊ : ℝ) ≤ n := by
      show (⌈4 * h * P2 / a⌉₊ : ℝ) ≤ (Fintype.card V : ℝ)
      exact_mod_cast (by omega : ⌈4 * h * P2 / a⌉₊ ≤ Fintype.card V)
    have h2 := (Nat.le_ceil (4 * h * P2 / a)).trans h1
    rw [div_le_iff₀ ha0] at h2; linarith
  have hθn : 0 ≤ θ * n := by positivity
  obtain ⟨hw1, hw2, -⟩ := windows_of (z := θ * n) (d := θ * n) (hh := h) hθ.le hP2 hθP.le
    hnpos.le hn1 hn2 hθn le_rfl le_rfl
  have hQ' : (1 - a) ^ Q ≤ θ ^ 2 / 16 :=
    (pow_le_pow_of_le_one (by linarith) (by linarith) hQ).trans hm0.le
  obtain ⟨y, hy⟩ := exists_sample ha0 hH3' hH4' ha1 hθ hθa rfl hnN hw1 hw2 hL hQ' hcs
  set W := baseW y.1
  set D := ⌊θ * n⌋₊
  set bad := univ.filter (fun v => BadRoot H F v y)
  set high := univ.filter (fun x => D < degIn (noThird H F W) x)
  set Z := (bad ∪ high) \ W
  have hZ : (Z.card : ℝ) ≤ θ * n / 4 := by
    have h1 : Z.card ≤ bad.card + high.card :=
      (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_union_le _ _)
    have h2 : ((Z.card : ℕ) : ℝ) ≤ bad.card + high.card := by exact_mod_cast h1
    exact h2.trans hy
  have hD : (D : ℝ) ≤ θ * n := Nat.floor_le hθn
  obtain ⟨w1, w2, w3⟩ := windows_of (z := Z.card) (d := D) (hh := h) hθ.le hP2 hθP.le
    hnpos.le hn1 hn2 (by positivity) (by linarith) hD
  refine hK H F (d := D) ha0 hH3' hH4' W Z (card_baseW_le _) Finset.disjoint_sdiff
    (fun v hvW hvZ => goodRoot_of_not_badRoot H F v y fun hb => hvZ
      (Finset.mem_sdiff.2 ⟨Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩),
        hvW⟩)) (fun x => ?_) w1 w2 w3
  by_cases hx : x ∈ W ∨ x ∈ Z
  · have : degIn (badEdges H F W Z) x = 0 := by
      unfold degIn
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hxe
      obtain ⟨-, -, hall, -⟩ := Finset.mem_filter.1 he
      rcases hx with hx | hx
      · exact (hall x hxe).1 hx
      · exact (hall x hxe).2 hx
    omega
  · push_neg at hx
    have hxh : x ∉ high := fun hxh => hx.2
      (Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ hxh, hx.1⟩)
    have : ¬ D < degIn (noThird H F W) x := fun hlt =>
      hxh (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩)
    exact (degIn_mono (badEdges_subset_noThird W Z) x).trans (by omega)

/-- **Absorbedor terminal desde H3–H4.** Composición de `uniformCert_of_H3H4` con
`slot_absorber_of_uniformCert`: las constantes `K` y `n₀` dependen sólo de `α` y `h`. -/
theorem slot_absorber_of_H3H4 (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ K n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
      n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
      ∀ (B : Finset (Sym2 V)) (d : ℕ), (∀ x, degIn B x ≤ d) → ∀ (P : Finset (Sym2 V)),
      IsPhysical H F P → ∀ (Z : Finset V), Inside Z P → ∀ (Ub : ℕ),
      Z.card + 3 * (K * P.card) + K * P.card * (2 * h - 2) +
        3 * (K * P.card) * (2 * h - 3) ≤ Ub →
      (Ub : ℝ) + 3 + 4 * d < α * Fintype.card V →
      ((Ub : ℝ) + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V →
      ∃ A, IsAbsorber H F A P ∧ Disjoint A B ∧
        A.card ≤ K * P.card * (4 * (2 * h - 2).choose 2 + 6) := by
  obtain ⟨K, n₀, hK⟩ := uniformCert_of_H3H4 α h hα
  exact ⟨K, n₀, fun H F hn hH3 hH4 B d hdeg P hP Z hPZ Ub hUb hw1 hw2 =>
    slot_absorber_of_uniformCert hα hH3 hH4 (hK H F hn hH3 hH4) B d hdeg P hP Z hPZ Ub hUb
      hw1 hw2⟩

end TypedTriangle
