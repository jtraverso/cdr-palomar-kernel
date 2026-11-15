/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.Absorption.BRIRatio
public import CDRBicolour.Absorption.Refined.GenSeed
public import CDRIIILib.KBicolor.Host

/-!
# A bounded right inverse for the `k`-class bicolour host (part 1: three-class sub-hosts)

For an injective `σ : Fin 3 → Fin k`, the points whose label lies in the image of `σ` form the
sub-host `Sub lab σ`, labelled by `subLab : Sub → Fin 3` with `σ ∘ subLab = lab`. Its allowed
(bicoloured) triangles are exactly the allowed triangles of the `k`-class host inside it
(`map_mem_triG`), so the three-class bounded right inverse (`bri_of_ratio`) transports:

* `push`: triangle weights of the sub-host to triangle weights of the host;
* `restr`: edge weights of the host to edge weights of the sub-host;
* `MincG_push_emap`, `MincG_push_out`: the incidence of a pushed weight is the incidence in the
  sub-host on its edges and `0` elsewhere;
* `ell_restr`: `ℓ` of a restricted weight supported in the sub-host is `ℓ` in the host;
* `csz_subLab`: the classes of the sub-host are classes of the host.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined

/-! ### Transport of triangle edges along embeddings -/

theorem triEdges_map_emb {α β : Type*} [DecidableEq α] [DecidableEq β] (φ : α ↪ β)
    (T : Finset α) :
    triEdges (T.map φ) = (triEdges T).map ⟨Sym2.map φ, Sym2.map.injective φ.injective⟩ := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
  simp only [triEdges, mem_filter, mk_mem_sym2_iff, mem_map, Sym2.mk_isDiag_iff,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, hne⟩
    refine ⟨s(x, y), ⟨by simp [hx, hy], ?_⟩, rfl⟩
    rw [Sym2.mk_isDiag_iff]; exact fun h => hne (by rw [h])
  · rintro ⟨e', ⟨he1, he2⟩, hmap⟩
    induction e' using Sym2.ind with
    | _ x y =>
    rw [mk_mem_sym2_iff] at he1
    rw [Sym2.mk_isDiag_iff] at he2
    rw [Sym2.map_mk, Sym2.eq_iff] at hmap
    rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨⟨x, he1.1, rfl⟩, ⟨y, he1.2, rfl⟩⟩, fun h => he2 (φ.injective h)⟩
    · exact ⟨⟨⟨y, he1.2, rfl⟩, ⟨x, he1.1, rfl⟩⟩, fun h => he2 (φ.injective h).symm⟩

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

/-- Weight of an edge in `ℓ` for any labelling: `-2` if monochromatic, `1` otherwise. -/
def wlk (lab : V → Fin k) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun u v => if lab u = lab v then (-2 : ℝ) else 1, fun u v => by simp [eq_comm]⟩ e

theorem map_mem_bicF {σ : Fin 3 → Fin k} (hσ : Function.Injective σ) (m : Multiset (Fin 3)) :
    m.map σ ∈ bicF k ↔ m ∈ cdrF := by
  change (Multiset.card (m.map σ) = 3 ∧ (m.map σ).toFinset.card = 2) ↔
    (Multiset.card m = 3 ∧ m.toFinset.card = 2)
  rw [Multiset.card_map, Multiset.toFinset_map, card_image_of_injective _ hσ]

section Sub

variable (lab : V → Fin k) (σ : Fin 3 → Fin k)

/-- Points whose label is in the image of `σ`. -/
abbrev Sub := {v : V // ∃ i, σ i = lab v}

/-- The three-class labelling of the sub-host. -/
def subLab (v : Sub lab σ) : Fin 3 := Classical.choose v.2

theorem subLab_spec (v : Sub lab σ) : σ (subLab lab σ v) = lab v.1 :=
  Classical.choose_spec v.2

/-- The inclusion of the sub-host. -/
def ιs : Sub lab σ ↪ V := Function.Embedding.subtype _

/-- Edges of the sub-host as edges of the host. -/
def emap (e : E0 (Sub lab σ)) : E0 V :=
  ⟨Sym2.map Subtype.val e.1, by rw [Sym2.isDiag_map Subtype.val_injective]; exact e.2⟩

theorem emap_injective : Function.Injective (emap lab σ) := by
  intro e e' h
  apply Subtype.ext
  exact Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h)

/-- Restriction of edge weights to the sub-host. -/
def restr : (E0 V → ℝ) →ₗ[ℝ] (E0 (Sub lab σ) → ℝ) where
  toFun g e := g (emap lab σ e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Push-forward of triangle weights of the sub-host. -/
def push : (Finset (Sub lab σ) → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun c T := ∑ T' ∈ univ.filter (fun T' : Finset (Sub lab σ) => T'.map (ιs lab σ) = T), c T'
  map_add' c c' := by ext T; simp [sum_add_distrib]
  map_smul' r c := by ext T; simp [mul_sum]

variable {lab σ}

theorem map_mem_triG (hσ : Function.Injective σ) (T' : Finset (Sub lab σ)) :
    T'.map (ιs lab σ) ∈ triG lab (bicF k) ↔ T' ∈ tri (subLab lab σ) := by
  have hval : (T'.map (ιs lab σ)).val.map lab = (T'.val.map (subLab lab σ)).map σ := by
    rw [map_val, Multiset.map_map, Multiset.map_map]
    congr 1
    funext v
    exact (subLab_spec lab σ v).symm
  simp only [triG, tri, allowed, IsAllowed, mem_filter, mem_univ, true_and, cHostG, cHost,
    SimpleGraph.top_adj, card_map, hval, map_mem_bicF hσ]
  constructor
  · rintro ⟨h3, -, hm⟩; exact ⟨h3, fun x _ y _ hxy => hxy, hm⟩
  · rintro ⟨h3, -, hm⟩; exact ⟨h3, fun x _ y _ hxy => hxy, hm⟩

theorem mem_triEdges_map_iff (T' : Finset (Sub lab σ)) (e : E0 V) :
    e.1 ∈ triEdges (T'.map (ιs lab σ)) ↔ ∃ e' : E0 (Sub lab σ), emap lab σ e' = e ∧ e'.1 ∈ triEdges T' := by
  rw [triEdges_map_emb, mem_map]
  constructor
  · rintro ⟨f, hf, hfe⟩
    have hnd : ¬ f.IsDiag := by
      intro hd; revert hf; unfold triEdges; simp [hd]
    refine ⟨⟨f, hnd⟩, Subtype.ext ?_, hf⟩
    exact hfe
  · rintro ⟨e', rfl, he'⟩
    exact ⟨e'.1, he', rfl⟩

/-- The incidence of a pushed weight, as a sum over the sub-host. -/
theorem MincG_push (y : Finset (Sub lab σ) → ℝ) (e : E0 V) :
    MincG lab (bicF k) (push lab σ y) e =
      ∑ T' ∈ univ.filter (fun T' : Finset (Sub lab σ) =>
        T'.map (ιs lab σ) ∈ triG lab (bicF k) ∧ e.1 ∈ triEdges (T'.map (ιs lab σ))), y T' := by
  simp only [MincG, push, LinearMap.coe_mk, AddHom.coe_mk]
  set S := (triG lab (bicF k)).filter (fun T => e.1 ∈ triEdges T)
  set s := univ.filter (fun T' : Finset (Sub lab σ) => T'.map (ιs lab σ) ∈ S)
  have hs : s = univ.filter (fun T' : Finset (Sub lab σ) =>
      T'.map (ιs lab σ) ∈ triG lab (bicF k) ∧ e.1 ∈ triEdges (T'.map (ιs lab σ))) := by
    ext T'; simp [s, S]
  rw [← hs]
  calc ∑ T ∈ S, ∑ T' ∈ univ.filter (fun T' : Finset (Sub lab σ) => T'.map (ιs lab σ) = T), y T'
      = ∑ T ∈ S, ∑ T' ∈ s.filter (fun T' => T'.map (ιs lab σ) = T), y T' := by
        refine sum_congr rfl fun T hT => ?_
        congr 1
        ext T'
        simp only [mem_filter, mem_univ, true_and, s]
        constructor
        · intro h; exact ⟨h ▸ hT, h⟩
        · exact fun h => h.2
    _ = ∑ T' ∈ s, y T' := sum_fiberwise_of_maps_to (fun T' hT' => (mem_filter.1 hT').2) _

theorem MincG_push_emap (hσ : Function.Injective σ) (y : Finset (Sub lab σ) → ℝ)
    (e' : E0 (Sub lab σ)) :
    MincG lab (bicF k) (push lab σ y) (emap lab σ e') = Minc (subLab lab σ) y e' := by
  rw [MincG_push]
  simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk]
  refine sum_congr ?_ fun _ _ => rfl
  ext T'
  simp only [mem_filter, mem_univ, true_and, map_mem_triG hσ, mem_triEdges_map_iff]
  constructor
  · rintro ⟨h1, f, hf, hfT⟩
    have : f = e' := emap_injective lab σ hf
    subst this
    exact ⟨h1, hfT⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, e', rfl, h2⟩

theorem MincG_push_out (y : Finset (Sub lab σ) → ℝ) (e : E0 V)
    (he : ∀ e' : E0 (Sub lab σ), emap lab σ e' ≠ e) :
    MincG lab (bicF k) (push lab σ y) e = 0 := by
  rw [MincG_push]
  apply sum_eq_zero
  intro T' hT'
  obtain ⟨f, hf, -⟩ := (mem_triEdges_map_iff T' e).1 (mem_filter.1 hT').2.2
  exact absurd hf (he f)

theorem card_push_fiber_le (T : Finset V) :
    #(univ.filter (fun T' : Finset (Sub lab σ) => T'.map (ιs lab σ) = T)) ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  exact map_injective (ιs lab σ) ((mem_filter.1 ha).2.trans (mem_filter.1 hb).2.symm)

theorem abs_push_le (y : Finset (Sub lab σ) → ℝ) {B : ℝ} (hB : 0 ≤ B) (hy : ∀ T', |y T'| ≤ B)
    (T : Finset V) : |push lab σ y T| ≤ B := by
  simp only [push, LinearMap.coe_mk, AddHom.coe_mk]
  calc |∑ T' ∈ univ.filter (fun T' : Finset (Sub lab σ) => T'.map (ιs lab σ) = T), y T'|
      ≤ ∑ T' ∈ univ.filter (fun T' : Finset (Sub lab σ) => T'.map (ιs lab σ) = T), |y T'| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _T' ∈ univ.filter (fun T' : Finset (Sub lab σ) => T'.map (ιs lab σ) = T), B :=
        sum_le_sum fun T' _ => hy T'
    _ = #(univ.filter (fun T' : Finset (Sub lab σ) => T'.map (ιs lab σ) = T)) * B := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast card_push_fiber_le T) hB
    _ = B := one_mul B

theorem norm_restr_le (g : E0 V → ℝ) : ‖restr lab σ g‖ ≤ ‖g‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg g)).2 fun e => norm_le_pi_norm g (emap lab σ e)

theorem wl_emap (hσ : Function.Injective σ) (e' : E0 (Sub lab σ)) :
    wl (subLab lab σ) e'.1 = wlk lab (emap lab σ e').1 := by
  obtain ⟨e, he⟩ := e'
  induction e using Sym2.ind with
  | _ u v =>
  simp only [emap, Sym2.map_mk, wl, wlk, Sym2.lift_mk]
  have : subLab lab σ u = subLab lab σ v ↔ lab u.1 = lab v.1 := by
    rw [← subLab_spec lab σ u, ← subLab_spec lab σ v]
    exact hσ.eq_iff.symm
  by_cases h : subLab lab σ u = subLab lab σ v
  · rw [if_pos h, if_pos (this.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]

/-- `ℓ` of a weight supported in the sub-host is `ℓ` of its restriction. -/
theorem ell_restr (hσ : Function.Injective σ) (g : E0 V → ℝ)
    (hg : ∀ e, g e ≠ 0 → ∃ e', emap lab σ e' = e) :
    ell (subLab lab σ) (restr lab σ g) = ellG' (wlk lab) g := by
  simp only [ell, ellG', restr, LinearMap.coe_mk, AddHom.coe_mk]
  have h1 : ∑ e' : E0 (Sub lab σ), wl (subLab lab σ) e'.1 * g (emap lab σ e') =
      ∑ e' : E0 (Sub lab σ), (fun e : E0 V => wlk lab e.1 * g e) (emap lab σ e') :=
    sum_congr rfl fun e' _ => by rw [wl_emap hσ]
  rw [h1]
  calc ∑ e', (fun e : E0 V => wlk lab e.1 * g e) (emap lab σ e')
      = ∑ e ∈ univ.map ⟨emap lab σ, emap_injective lab σ⟩, wlk lab e.1 * g e :=
        (sum_map univ ⟨emap lab σ, emap_injective lab σ⟩
          (fun e : E0 V => wlk lab e.1 * g e)).symm
    _ = ∑ e, wlk lab e.1 * g e := by
        apply sum_subset (subset_univ _)
        intro e _ he
        have : g e = 0 := by
          by_contra hne
          obtain ⟨e', rfl⟩ := hg e hne
          exact he (mem_map.2 ⟨e', mem_univ _, rfl⟩)
        simp [this]

/-- The classes of the sub-host are classes of the host. -/
theorem csz_subLab (hσ : Function.Injective σ) (i : Fin 3) :
    csz (subLab lab σ) i = ksz lab (σ i) := by
  unfold csz ksz
  apply card_bij (fun v _ => v.1)
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    rw [← hv, subLab_spec lab σ v]
  · intro v _ w _ h; exact Subtype.ext h
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    refine ⟨⟨v, i, hv.symm⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    apply hσ
    rw [subLab_spec lab σ ⟨v, i, hv.symm⟩]
    exact hv

end Sub

end CDRBicolour.KBicolor
