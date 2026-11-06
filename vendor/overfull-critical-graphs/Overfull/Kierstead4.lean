/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Shift

/-!
# Kierstead paths with four vertices

CCJS Lemma 2.4 (Kostochka–Stiebitz; Stiebitz–Scheide–Toft–Favrholdt, Theorem 3.3). For a
Kierstead path `a b u v` with respect to the uncoloured edge `ab`:

* (a) if `d(b) < Δ` or `d(u) < Δ`, then `{a, b, u, v}` is elementary;
* (b) at most one colour missing at `a` or `b` is missing at `v`.

The proof here does not follow the book. Its tools are the multifan lemma, Kempe swaps of the
`a`–`b` chain (which keep `φ̄(a) ∪ φ̄(b)` and `φ̄(v)`), and moving the uncoloured edge to `bu`; see
`NOTES_KIERSTEAD4.md`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A Kierstead path `a b u v` for the uncoloured edge `ab`, with `δ = φ(bu)` and `γ = φ(uv)`. -/
structure IsK4 {k : ℕ} (c : PEC G (Fin k)) (a b u v : V) (δ γ : Fin k) : Prop where
  cm : IsColMinus c a b
  bu : c.col b u = some δ
  uv : c.col u v = some γ
  freeδ : c.IsFree a δ
  freeγ : c.IsFree a γ ∨ c.IsFree b γ
  au : a ≠ u
  av : a ≠ v
  bv : b ≠ v

namespace IsK4

variable {k : ℕ} {c : PEC G (Fin k)} {a b u v : V} {δ γ : Fin k}

theorem adj_bu (h : IsK4 c a b u v δ γ) : G.Adj b u := c.col_adj h.bu

theorem adj_uv (h : IsK4 c a b u v δ γ) : G.Adj u v := c.col_adj h.uv

theorem ab (h : IsK4 c a b u v δ γ) : a ≠ b := h.cm.adj.ne

theorem bu_ne (h : IsK4 c a b u v δ γ) : b ≠ u := h.adj_bu.ne

theorem uv_ne (h : IsK4 c a b u v δ γ) : u ≠ v := h.adj_uv.ne

theorem δ_ne_γ (h : IsK4 c a b u v δ γ) : δ ≠ γ := by
  rintro rfl
  have h1 : c.col u b = some δ := by rw [c.col_symm]; exact h.bu
  exact h.bv (c.col_proper h1 h.uv)

theorem not_free_v_γ (h : IsK4 c a b u v δ γ) : ¬ c.IsFree v γ := fun hv =>
  hv u (by rw [c.col_symm]; exact h.uv)

theorem not_free_u_γ (h : IsK4 c a b u v δ γ) : ¬ c.IsFree u γ := fun hu => hu v h.uv

theorem not_free_b_δ (h : IsK4 c a b u v δ γ) : ¬ c.IsFree b δ := fun hb => hb u h.bu

end IsK4

/-! ### Colourings of `G − ab` -/

/-- Kempe swaps keep a colouring of `G − ab`. -/
theorem IsColMinus.kempeSwap {k : ℕ} {c : PEC G (Fin k)} {a b : V} (hcm : IsColMinus c a b)
    (α β : Fin k) (w : V) : IsColMinus (c.kempeSwap α β w) a b :=
  ⟨hcm.adj, kempeSwap_col_none c α β w hcm.uncol,
    fun x y hxy hne => extends_kempeSwap c α β w x y (hcm.total x y hxy hne)⟩

theorem kempeGraph_comm {k : ℕ} (c : PEC G (Fin k)) (α β : Fin k) :
    c.kempeGraph α β = c.kempeGraph β α := by
  ext x y
  simp only [kempeGraph_adj]
  tauto

/-- The ends of the uncoloured edge: no common missing colour, and linked by every pair. -/
theorem IsColMinus.ab_facts (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b : V}
    (hcm : IsColMinus c a b) :
    (∀ θ, c.IsFree a θ → ¬ c.IsFree b θ) ∧
    (∀ θ μ, c.IsFree a θ → c.IsFree b μ → (c.kempeGraph θ μ).Reachable a b) := by
  have hF : IsMultifan c b 1 (fun _ => a) :=
    ⟨Nat.one_pos, by rw [c.col_symm]; exact hcm.uncol, fun _ _ => hcm.adj.symm,
      fun i hi j hj _ => by omega, fun i hi hi' => by omega⟩
  obtain ⟨hA, -, hB⟩ := multifan_elementary hG 1 c b (fun _ => a) hcm.symm hF
  refine ⟨fun θ ha hb => hA 0 Nat.one_pos θ hb ha, fun θ μ ha hb => ?_⟩
  have := hB 0 Nat.one_pos μ θ hb ha
  rw [kempeGraph_comm]
  exact this.symm

/-- Swapping a Kempe chain through both ends `a, b` keeps the missing colours of every other
vertex. -/
theorem isFree_kempeSwap_of_linked {k : ℕ} (c : PEC G (Fin k)) {θ μ : Fin k} {a b w : V}
    (hab : (c.kempeGraph θ μ).Reachable a b) (ha : c.IsFree a θ ∨ c.IsFree a μ)
    (hb : c.IsFree b θ ∨ c.IsFree b μ) (hwa : w ≠ a) (hwb : w ≠ b) (hne : a ≠ b) (ε : Fin k) :
    (c.kempeSwap θ μ a).IsFree w ε ↔ c.IsFree w ε := by
  by_cases hr : (c.kempeGraph θ μ).Reachable a w
  · have hw : ¬ c.IsFree w θ ∧ ¬ c.IsFree w μ := by
      constructor <;> intro hw
      · exact not_three_linked c hne hwa.symm hwb.symm ha hb (Or.inl hw) hab hr
      · exact not_three_linked c hne hwa.symm hwb.symm ha hb (Or.inr hw) hab hr
    rw [isFree_kempeSwap_of_reachable c θ μ hr]
    by_cases h1 : ε = θ
    · subst h1
      rw [Equiv.swap_apply_left]
      exact ⟨fun h => absurd h hw.2, fun h => absurd h hw.1⟩
    by_cases h2 : ε = μ
    · subst h2
      rw [Equiv.swap_apply_right]
      exact ⟨fun h => absurd h hw.1, fun h => absurd h hw.2⟩
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  · exact isFree_kempeSwap_of_not_reachable c θ μ hr ε

/-! ### The multifan `(b; a, u)` -/

theorem fan_bau (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u : V} {δ : Fin G.maxDegree}
    (hcm : IsColMinus c a b) (hbu : c.col b u = some δ) (hδ : c.IsFree a δ) (hau : a ≠ u) :
    (∀ θ, c.IsFree a θ → ¬ c.IsFree u θ) ∧ (∀ θ, c.IsFree b θ → ¬ c.IsFree u θ) := by
  have hF : IsMultifan c b 2 (fun i => if i = 0 then a else u) := by
    refine ⟨by omega, by simp only [if_true]; rw [c.col_symm]; exact hcm.uncol,
      fun i hi => ?_, fun i hi j hj hij => ?_, fun i hi0 hi => ?_⟩
    · split_ifs
      · exact hcm.adj.symm
      · exact c.col_adj hbu
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rfl
      · exact absurd hij (by simpa using hau)
      · exact absurd hij (by simpa using hau.symm)
      · rfl
    · refine ⟨0, hi0, δ, ?_, by simpa using hδ⟩
      simp only [show i ≠ 0 by omega, if_false]
      exact hbu
  obtain ⟨hA, hA', -⟩ := multifan_elementary hG 2 c b _ hcm.symm hF
  exact ⟨fun θ ha hu => hA' 0 (by omega) 1 (by omega) (by omega) θ (by simpa using ha)
    (by simpa using hu), fun θ hb hu => hA 1 (by omega) θ hb (by simpa using hu)⟩

/-- **L1.** `u` and `v` have no common missing colour. -/
theorem IsK4.not_free_u_v (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ) (θ : Fin G.maxDegree) (hu : c.IsFree u θ) :
    ¬ c.IsFree v θ := by
  intro hv
  set c' := c.setEdge θ h.adj_uv hu hv
  have hcm' : IsColMinus c' a b :=
    ⟨h.cm.adj, by
      rw [setEdge_col, updFun_of_ne _ (by have := h.au; have := h.av; tauto)]
      exact h.cm.uncol,
      fun x y hxy hne => extends_setEdge c θ h.adj_uv hu hv x y (h.cm.total x y hxy hne)⟩
  have hbu' : c'.col b u = some δ := by
    rw [setEdge_col, updFun_of_ne _ (by have := h.bu_ne; have := h.bv; tauto)]
    exact h.bu
  have hδ' : c'.IsFree a δ := (isFree_setEdge_of_ne c θ h.adj_uv hu hv h.au h.av δ).2 h.freeδ
  obtain ⟨hA, hB⟩ := fan_bau hG hcm' hbu' hδ' h.au
  have hγu : c'.IsFree u γ := isFree_setEdge_old c θ h.adj_uv hu hv h.uv
  rcases h.freeγ with hγ | hγ
  · exact hA γ ((isFree_setEdge_of_ne c θ h.adj_uv hu hv h.au h.av γ).2 hγ) hγu
  · exact hB γ ((isFree_setEdge_of_ne c θ h.adj_uv hu hv h.bu_ne h.bv γ).2 hγ) hγu

/-! ### Moving the uncoloured edge from `ab` to `bu` -/

/-- Colour `ab` with `δ = φ(bu)` and uncolour `bu`. -/
theorem exists_shift {k : ℕ} {c : PEC G (Fin k)} {a b u : V} {δ : Fin k}
    (hcm : IsColMinus c a b) (hbu : c.col b u = some δ) (hδa : c.IsFree a δ) (hau : a ≠ u) :
    ∃ ψ : PEC G (Fin k), IsColMinus ψ u b ∧ ψ.col a b = some δ ∧
      (∀ x y, ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) → ¬ ((x = b ∧ y = u) ∨ (x = u ∧ y = b)) →
        ψ.col x y = c.col x y) ∧
      (∀ μ, ψ.IsFree b μ ↔ c.IsFree b μ) ∧ ψ.IsFree u δ ∧
      (∀ w, w ≠ a → w ≠ b → w ≠ u → ∀ μ, ψ.IsFree w μ ↔ c.IsFree w μ) := by
  have hab : a ≠ b := hcm.adj.ne
  have hbu' : b ≠ u := (c.col_adj hbu).ne
  have hb1 : (unsetEdge c b u).IsFree b δ := (isFree_unsetEdge_left c hbu' hbu δ).2 (Or.inl rfl)
  have ha1 : (unsetEdge c b u).IsFree a δ := (isFree_unsetEdge_of_ne c hab hau δ).2 hδa
  set ψ := (unsetEdge c b u).setEdge δ hcm.adj ha1 hb1
  have hcol : ∀ x y, ψ.col x y = if (x = a ∧ y = b) ∨ (x = b ∧ y = a) then some δ else
      if (x = b ∧ y = u) ∨ (x = u ∧ y = b) then none else c.col x y := fun x y => rfl
  have hoff : ∀ x y, ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) →
      ¬ ((x = b ∧ y = u) ∨ (x = u ∧ y = b)) → ψ.col x y = c.col x y := by
    intro x y h1 h2
    rw [hcol, if_neg h1, if_neg h2]
  have hδb : ¬ c.IsFree b δ := fun hb => hb u hbu
  refine ⟨ψ, ⟨(c.col_adj hbu).symm, ?_, ?_⟩, ?_, hoff, fun μ => ?_, ?_, ?_⟩
  · rw [hcol, if_neg (by tauto), if_pos (Or.inr ⟨rfl, rfl⟩)]
  · intro x y hxy hne
    rw [hcol]
    split_ifs with h1 h2
    · exact Option.some_ne_none _
    · exact absurd (by rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Sym2.eq_swap]) hne
    · exact hcm.total x y hxy (fun he => h1 (by
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto))
  · rw [hcol, if_pos (Or.inl ⟨rfl, rfl⟩)]
  · constructor
    · intro h w hw
      by_cases hwu : w = u
      · subst hwu
        rw [hbu] at hw
        have := Option.some_injective _ hw
        subst this
        exact h a (by rw [hcol, if_pos (Or.inr ⟨rfl, rfl⟩)])
      by_cases hwa : w = a
      · subst hwa
        rw [c.col_symm, hcm.uncol] at hw
        cases hw
      exact h w (by rw [hoff b w (by tauto) (by tauto)]; exact hw)
    · intro h w hw
      by_cases hwu : w = u
      · subst hwu
        rw [hcol, if_neg (by tauto), if_pos (Or.inl ⟨rfl, rfl⟩)] at hw
        cases hw
      by_cases hwa : w = a
      · subst hwa
        rw [hcol, if_pos (Or.inr ⟨rfl, rfl⟩)] at hw
        have := Option.some_injective _ hw
        subst this
        exact hδb h
      exact h w (by rw [hoff b w (by tauto) (by tauto)] at hw; exact hw)
  · intro w hw
    by_cases hwb : w = b
    · subst hwb
      rw [hcol, if_neg (by tauto), if_pos (Or.inr ⟨rfl, rfl⟩)] at hw
      cases hw
    rw [hoff u w (by tauto) (by tauto)] at hw
    rw [c.col_symm] at hbu
    exact hwb (c.col_proper hw hbu)
  · intro w hwa hwb hwu μ
    constructor <;> intro h x hx
    · exact h x (by rw [hoff w x (by tauto) (by tauto)]; exact hx)
    · rw [hoff w x (by tauto) (by tauto)] at hx
      exact h x hx

/-- **L2.** If `φ(uv)` is missing at `b`, then neither `φ(bu)` nor a colour missing at `b` is
missing at `v`. -/
theorem IsK4.type1 (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ) (hγb : c.IsFree b γ) :
    ¬ c.IsFree v δ ∧ ∀ θ, c.IsFree b θ → ¬ c.IsFree v θ := by
  obtain ⟨ψ, hcm, -, hoff, hb, hu, hw⟩ := exists_shift h.cm h.bu h.freeδ h.au
  have hψuv : ψ.col u v = some γ := by
    rw [hoff u v (by have := h.au; have := h.bu_ne; tauto)
      (by have := h.bu_ne; have := h.bv; tauto)]
    exact h.uv
  have hF : IsMultifan ψ u 2 (fun i => if i = 0 then b else v) := by
    refine ⟨by omega, by simp only [if_true]; exact hcm.uncol, fun i hi => ?_,
      fun i hi j hj hij => ?_, fun i hi0 hi => ?_⟩
    · split_ifs
      · exact h.adj_bu.symm
      · exact h.adj_uv
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rfl
      · exact absurd hij (by simpa using h.bv)
      · exact absurd hij (by simpa using h.bv.symm)
      · rfl
    · refine ⟨0, hi0, γ, ?_, by simpa using (hb γ).2 hγb⟩
      simp only [show i ≠ 0 by omega, if_false]
      exact hψuv
  obtain ⟨hA, hA', -⟩ := multifan_elementary hG 2 ψ u _ hcm hF
  have hv : ∀ μ, ψ.IsFree v μ ↔ c.IsFree v μ := hw v h.av.symm h.bv.symm h.uv_ne.symm
  exact ⟨fun hδ => hA 1 (by omega) δ hu (by simpa using (hv δ).2 hδ),
    fun θ hθ hθv => hA' 0 (by omega) 1 (by omega) (by omega) θ (by simpa using (hb θ).2 hθ)
      (by simpa using (hv θ).2 hθv)⟩

/-! ### Swapping the `a`–`b` chain -/

/-- **Redistribution.** For `θ` missing at `a` and `μ` missing at `b`, swapping the `(θ, μ)`-chain
through `a` and `b` moves `θ` to `b` and `μ` to `a`, keeps `φ̄(a) ∪ φ̄(b)` and the missing colours
of all other vertices, and changes edge colours only on that chain. -/
theorem IsColMinus.redistribute (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b : V}
    (hcm : IsColMinus c a b) {θ μ : Fin G.maxDegree} (hθ : c.IsFree a θ) (hμ : c.IsFree b μ) :
    ∃ c' : PEC G (Fin G.maxDegree), IsColMinus c' a b ∧ c'.IsFree a μ ∧ c'.IsFree b θ ∧
      (∀ ε, ε ≠ θ → ε ≠ μ → (c'.IsFree a ε ↔ c.IsFree a ε) ∧ (c'.IsFree b ε ↔ c.IsFree b ε)) ∧
      (∀ ε, (c'.IsFree a ε ∨ c'.IsFree b ε) ↔ (c.IsFree a ε ∨ c.IsFree b ε)) ∧
      (∀ w, w ≠ a → w ≠ b → ∀ ε, c'.IsFree w ε ↔ c.IsFree w ε) ∧
      (∀ x y ε, c.col x y = some ε → ε ≠ θ → ε ≠ μ → c'.col x y = some ε) ∧
      (∀ y, c.col b y = some θ → c'.col b y = some μ) ∧
      (∀ x y ε, c.col x y = some ε → ¬ (c.kempeGraph θ μ).Reachable a x →
        c'.col x y = some ε) ∧
      (c.kempeGraph θ μ).Reachable a b := by
  obtain ⟨hdis, hlink⟩ := hcm.ab_facts hG
  have hab := hlink θ μ hθ hμ
  have hne : a ≠ b := hcm.adj.ne
  have hθμ : θ ≠ μ := fun he => hdis θ hθ (he ▸ hμ)
  have hfa : ∀ ε, (c.kempeSwap θ μ a).IsFree a ε ↔ c.IsFree a (Equiv.swap θ μ ε) :=
    isFree_kempeSwap_of_reachable c θ μ (Reachable.refl a)
  have hfb : ∀ ε, (c.kempeSwap θ μ a).IsFree b ε ↔ c.IsFree b (Equiv.swap θ μ ε) :=
    isFree_kempeSwap_of_reachable c θ μ hab
  refine ⟨c.kempeSwap θ μ a, hcm.kempeSwap θ μ a, by rw [hfa, Equiv.swap_apply_right]; exact hθ,
    by rw [hfb, Equiv.swap_apply_left]; exact hμ, fun ε h1 h2 => ⟨?_, ?_⟩, fun ε => ?_,
    fun w hwa hwb ε => isFree_kempeSwap_of_linked c hab (Or.inl hθ) (Or.inr hμ) hwa hwb hne ε,
    fun x y ε hxy h1 h2 => kempeSwap_col_of_ne c θ μ a x y hxy h1 h2, fun y hy => ?_,
    fun x y ε hxy hx => ?_, hab⟩
  · rw [hfa, Equiv.swap_apply_of_ne_of_ne h1 h2]
  · rw [hfb, Equiv.swap_apply_of_ne_of_ne h1 h2]
  · rw [hfa, hfb]
    by_cases h1 : ε = θ
    · subst h1
      rw [Equiv.swap_apply_left]
      exact ⟨fun _ => Or.inl hθ, fun _ => Or.inr hμ⟩
    by_cases h2 : ε = μ
    · subst h2
      rw [Equiv.swap_apply_right]
      exact ⟨fun _ => Or.inr hμ, fun _ => Or.inl hθ⟩
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  · rw [kempeSwap_col, kempeSwapFun_of_reachable c θ μ hab y, hy]
    simp
  · rw [kempeSwap_col, kempeSwapFun_of_not_reachable c θ μ hx y, hxy]

/-! ### From `φ(uv)` missing at `a` to `φ(uv)` missing at `b` -/

/-- **Step 2.** If `φ(uv) = γ` is missing at `a` and `θ` is missing at `b` and at `v`, swapping the
`(γ, θ)`-chain at `v` recolours `uv` with `θ` and fixes `a`, `b` and `bu`. -/
theorem IsK4.step2 (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ) (hγa : c.IsFree a γ)
    {θ : Fin G.maxDegree} (hθb : c.IsFree b θ) (hθv : c.IsFree v θ) :
    ∃ c' : PEC G (Fin G.maxDegree), IsK4 c' a b u v δ θ ∧ c'.IsFree b θ ∧ c'.IsFree v γ ∧
      (∀ ε, ε ≠ γ → ε ≠ θ → (c'.IsFree v ε ↔ c.IsFree v ε)) ∧
      (∀ ε, c'.IsFree a ε ↔ c.IsFree a ε) ∧ (∀ ε, c'.IsFree b ε ↔ c.IsFree b ε) := by
  obtain ⟨hdis, hlink⟩ := h.cm.ab_facts hG
  have hab := hlink γ θ hγa hθb
  have hva : ¬ (c.kempeGraph γ θ).Reachable v a := fun r =>
    not_three_linked c h.ab h.av h.bv (Or.inl hγa) (Or.inr hθb) (Or.inr hθv) hab r.symm
  have hvb : ¬ (c.kempeGraph γ θ).Reachable v b := fun r => hva (r.trans hab.symm)
  have hδγ : δ ≠ γ := h.δ_ne_γ
  have hδθ : δ ≠ θ := fun he => hdis δ h.freeδ (he ▸ hθb)
  have hvu : (c.kempeGraph γ θ).Reachable v u :=
    (kempeGraph_adj_of_col (Or.inl (by rw [c.col_symm]; exact h.uv))).reachable
  have ha := isFree_kempeSwap_of_not_reachable c γ θ hva
  have hb := isFree_kempeSwap_of_not_reachable c γ θ hvb
  refine ⟨c.kempeSwap γ θ v, ⟨h.cm.kempeSwap γ θ v,
    kempeSwap_col_of_ne c γ θ v b u h.bu hδγ hδθ, ?_, (ha δ).2 h.freeδ, Or.inr ((hb θ).2 hθb),
    h.au, h.av, h.bv⟩, (hb θ).2 hθb, ?_, fun ε h1 h2 => kempeSwap_isFree_of_ne c γ θ v v h1 h2,
    ha, hb⟩
  · rw [kempeSwap_col, kempeSwapFun_of_reachable c γ θ hvu v, h.uv]
    simp
  · rw [isFree_kempeSwap_of_reachable c γ θ (Reachable.refl v), Equiv.swap_apply_left]
    exact hθv

/-- **Key lemma.** If `φ(uv)` is missing at `a`, then `φ(bu)` and a colour missing at `b` are not
both missing at `v`. -/
theorem IsK4.key (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ) (hγa : c.IsFree a γ) (hδv : c.IsFree v δ)
    {θ : Fin G.maxDegree} (hθb : c.IsFree b θ) (hθv : c.IsFree v θ) : False := by
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  obtain ⟨c', h', hθb', -, hv', -, -⟩ := h.step2 hG hγa hθb hθv
  exact (h'.type1 hG hθb').1 ((hv' δ h.δ_ne_γ (fun he => hdis δ h.freeδ (he ▸ hθb))).2 hδv)

/-! ### Part (b): at most one colour of `φ̄(a) ∪ φ̄(b)` is missing at `v` -/

/-- Case C: `φ(uv)` and `φ(bu)` missing at `a`, `φ(bu)` and a second colour of `Γ` missing at
`v`. -/
theorem IsK4.caseC (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ) (hγa : c.IsFree a γ) (hδv : c.IsFree v δ)
    {θ : Fin G.maxDegree} (hθ : c.IsFree a θ ∨ c.IsFree b θ) (hθv : c.IsFree v θ) (hθδ : θ ≠ δ) :
    False := by
  rcases hθ with hθa | hθb
  · obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
    obtain ⟨μ, hμ⟩ := h.cm.exists_free_right
    obtain ⟨c', hcm', -, hθb', hinv, -, hw, hcol, -, -, -⟩ := h.cm.redistribute hG hθa hμ
    have hδμ : δ ≠ μ := fun he => hdis δ h.freeδ (he ▸ hμ)
    have hγθ : γ ≠ θ := fun he => h.not_free_v_γ (he ▸ hθv)
    have hγμ : γ ≠ μ := fun he => hdis γ hγa (he ▸ hμ)
    have hv := hw v h.av.symm h.bv.symm
    have h' : IsK4 c' a b u v δ γ :=
      ⟨hcm', hcol b u δ h.bu hθδ.symm hδμ, hcol u v γ h.uv hγθ hγμ,
        ((hinv δ hθδ.symm hδμ).1).2 h.freeδ, Or.inl (((hinv γ hγθ hγμ).1).2 hγa), h.au, h.av,
        h.bv⟩
    exact h'.key hG (((hinv γ hγθ hγμ).1).2 hγa) ((hv δ).2 hδv) hθb' ((hv θ).2 hθv)
  · exact h.key hG hγa hδv hθb hθv

/-- Case B0: `φ(uv)` missing at `a`; `θ` missing at `b` and at `v`; a second colour of `Γ` missing
at `v`. -/
theorem IsK4.caseB0 (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ) (hγa : c.IsFree a γ)
    {θ θ' : Fin G.maxDegree} (hθb : c.IsFree b θ) (hθv : c.IsFree v θ)
    (hθ' : c.IsFree a θ' ∨ c.IsFree b θ') (hθ'v : c.IsFree v θ') (hne : θ ≠ θ') : False := by
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have hθδ : θ ≠ δ := fun he => h.not_free_b_δ (he ▸ hθb)
  by_cases hδv : c.IsFree v δ
  · exact h.caseC hG hγa hδv (Or.inr hθb) hθv hθδ
  obtain ⟨c', hcm', hθa', -, hinv, hΓ, hw, hcol, hflip, -, -⟩ :=
    h.cm.redistribute hG h.freeδ hθb
  have hγδ : γ ≠ δ := h.δ_ne_γ.symm
  have hγθ : γ ≠ θ := fun he => h.not_free_v_γ (he ▸ hθv)
  have hv := hw v h.av.symm h.bv.symm
  have h' : IsK4 c' a b u v θ γ :=
    ⟨hcm', hflip u h.bu, hcol u v γ h.uv hγδ hγθ, hθa', Or.inl (((hinv γ hγδ hγθ).1).2 hγa),
      h.au, h.av, h.bv⟩
  exact h'.caseC hG (((hinv γ hγδ hγθ).1).2 hγa) ((hv θ).2 hθv) ((hΓ θ').2 hθ') ((hv θ').2 hθ'v)
    hne.symm

/-- Case B: `φ(uv)` missing at `a`. -/
theorem IsK4.caseB (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ) (hγa : c.IsFree a γ)
    {θ₁ θ₂ : Fin G.maxDegree} (hne : θ₁ ≠ θ₂) (h₁ : c.IsFree a θ₁ ∨ c.IsFree b θ₁)
    (h₂ : c.IsFree a θ₂ ∨ c.IsFree b θ₂) (hv₁ : c.IsFree v θ₁) (hv₂ : c.IsFree v θ₂) : False := by
  by_cases hb₁ : c.IsFree b θ₁
  · exact h.caseB0 hG hγa hb₁ hv₁ h₂ hv₂ hne
  by_cases hb₂ : c.IsFree b θ₂
  · exact h.caseB0 hG hγa hb₂ hv₂ h₁ hv₁ hne.symm
  have ha₁ : c.IsFree a θ₁ := h₁.resolve_right hb₁
  by_cases hδ₁ : θ₁ = δ
  · subst hδ₁
    exact h.caseC hG hγa hv₁ h₂ hv₂ hne.symm
  by_cases hδ₂ : θ₂ = δ
  · subst hδ₂
    exact h.caseC hG hγa hv₂ h₁ hv₁ hne
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  obtain ⟨μ, hμ⟩ := h.cm.exists_free_right
  obtain ⟨c', hcm', -, hθb', hinv, hΓ, hw, hcol, -, -, -⟩ := h.cm.redistribute hG ha₁ hμ
  have hδμ : δ ≠ μ := fun he => hdis δ h.freeδ (he ▸ hμ)
  have hγθ : γ ≠ θ₁ := fun he => h.not_free_v_γ (he ▸ hv₁)
  have hγμ : γ ≠ μ := fun he => hdis γ hγa (he ▸ hμ)
  have hv := hw v h.av.symm h.bv.symm
  have h' : IsK4 c' a b u v δ γ :=
    ⟨hcm', hcol b u δ h.bu (Ne.symm hδ₁) hδμ, hcol u v γ h.uv hγθ hγμ,
      ((hinv δ (Ne.symm hδ₁) hδμ).1).2 h.freeδ, Or.inl (((hinv γ hγθ hγμ).1).2 hγa), h.au,
      h.av, h.bv⟩
  exact h'.caseB0 hG (((hinv γ hγθ hγμ).1).2 hγa) hθb' ((hv θ₁).2 hv₁) ((hΓ θ₂).2 h₂)
    ((hv θ₂).2 hv₂) hne

/-- Case A: `φ(uv)` missing at `b`. -/
theorem IsK4.caseA (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ) (hγb : c.IsFree b γ)
    {θ₁ θ₂ : Fin G.maxDegree} (hne : θ₁ ≠ θ₂) (h₁ : c.IsFree a θ₁ ∨ c.IsFree b θ₁)
    (h₂ : c.IsFree a θ₂ ∨ c.IsFree b θ₂) (hv₁ : c.IsFree v θ₁) (hv₂ : c.IsFree v θ₂) : False := by
  obtain ⟨hδv, hbv⟩ := h.type1 hG hγb
  have ha₁ : c.IsFree a θ₁ := h₁.resolve_right fun hb => hbv θ₁ hb hv₁
  have hδθ : δ ≠ θ₁ := fun he => hδv (he ▸ hv₁)
  obtain ⟨c', hcm', hγa', -, hinv, hΓ, hw, hcol, -, hfix, hab⟩ := h.cm.redistribute hG ha₁ hγb
  have hu : ¬ (c.kempeGraph θ₁ γ).Reachable a u := fun r =>
    not_three_linked c h.ab h.av h.bv (Or.inl ha₁) (Or.inr hγb) (Or.inl hv₁) hab
      (reachable_of_col r (Or.inr h.uv))
  have hv := hw v h.av.symm h.bv.symm
  have h' : IsK4 c' a b u v δ γ :=
    ⟨hcm', hcol b u δ h.bu hδθ h.δ_ne_γ, hfix u v γ h.uv hu,
      ((hinv δ hδθ h.δ_ne_γ).1).2 h.freeδ, Or.inl hγa', h.au, h.av, h.bv⟩
  exact h'.caseB hG hγa' hne ((hΓ θ₁).2 h₁) ((hΓ θ₂).2 h₂) ((hv θ₁).2 hv₁) ((hv θ₂).2 hv₂)

/-- **CCJS Lemma 2.4 (b)** (Kostochka–Stiebitz). For a Kierstead path `a b u v`, at most one colour
missing at `a` or `b` is missing at `v`. -/
theorem IsK4.not_two_common (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ) {θ₁ θ₂ : Fin G.maxDegree} (hne : θ₁ ≠ θ₂)
    (h₁ : c.IsFree a θ₁ ∨ c.IsFree b θ₁) (h₂ : c.IsFree a θ₂ ∨ c.IsFree b θ₂)
    (hv₁ : c.IsFree v θ₁) (hv₂ : c.IsFree v θ₂) : False := by
  rcases h.freeγ with hγa | hγb
  · exact h.caseB hG hγa hne h₁ h₂ hv₁ hv₂
  · exact h.caseA hG hγb hne h₁ h₂ hv₁ hv₂

open Classical in
theorem IsK4.card_common_le_one (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ) :
    #((missing c v).filter fun θ => c.IsFree a θ ∨ c.IsFree b θ) ≤ 1 := by
  rw [card_le_one]
  intro θ₁ h₁ θ₂ h₂
  simp only [mem_filter, mem_missing] at h₁ h₂
  by_contra hne
  exact h.not_two_common hG hne h₁.2 h₂.2 h₁.1 h₂.1

/-! ### Part (a): `d(b) < Δ` or `d(u) < Δ` -/

/-- An end of the uncoloured edge of degree below `Δ` misses two colours. -/
theorem IsColMinus.two_free_right {c : PEC G (Fin G.maxDegree)} {a b : V} (hcm : IsColMinus c a b)
    (hdeg : G.degree b < G.maxDegree) : ∃ μ ν, μ ≠ ν ∧ c.IsFree b μ ∧ c.IsFree b ν := by
  have h1 := card_missing_add_colNbrs c b
  have h2 := hcm.card_colNbrs b
  simp only [or_true, if_true] at h2
  obtain ⟨μ, hμ, ν, hν, hne⟩ := one_lt_card.1 (show 1 < #(missing c b) by omega)
  exact ⟨μ, ν, hne, mem_missing.1 hμ, mem_missing.1 hν⟩

/-- Type 1 with a second colour missing at `b`: no colour of `Γ` is missing at `v`. -/
theorem IsK4.typeA1 (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ) (hγb : c.IsFree b γ)
    {μ : Fin G.maxDegree} (hμ : c.IsFree b μ) (hμγ : μ ≠ γ)
    {θ : Fin G.maxDegree} (hθ : c.IsFree a θ ∨ c.IsFree b θ) (hθv : c.IsFree v θ) : False := by
  obtain ⟨hδv, hbv⟩ := h.type1 hG hγb
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have hθa : c.IsFree a θ := hθ.resolve_right fun hb => hbv θ hb hθv
  have hδθ : δ ≠ θ := fun he => hδv (he ▸ hθv)
  have hδμ : δ ≠ μ := fun he => hdis δ h.freeδ (he ▸ hμ)
  have hγθ : γ ≠ θ := fun he => h.not_free_v_γ (he ▸ hθv)
  obtain ⟨c', hcm', -, hθb', hinv, -, hw, hcol, -, -, -⟩ := h.cm.redistribute hG hθa hμ
  have hγb' : c'.IsFree b γ := ((hinv γ hγθ hμγ.symm).2).2 hγb
  have h' : IsK4 c' a b u v δ γ :=
    ⟨hcm', hcol b u δ h.bu hδθ hδμ, hcol u v γ h.uv hγθ hμγ.symm,
      ((hinv δ hδθ hδμ).1).2 h.freeδ, Or.inr hγb', h.au, h.av, h.bv⟩
  exact (h'.type1 hG hγb').2 θ hθb' ((hw v h.av.symm h.bv.symm θ).2 hθv)

/-- Type 0, `θ` missing at `b` and `v`, and a second colour missing at `b`: contradiction. -/
theorem IsK4.typeT0b (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ) (hγa : c.IsFree a γ)
    {θ : Fin G.maxDegree} (hθb : c.IsFree b θ) (hθv : c.IsFree v θ)
    {μ : Fin G.maxDegree} (hμ : c.IsFree b μ) (hμθ : μ ≠ θ) : False := by
  obtain ⟨c', h', hθb', hγv', -, ha', hb'⟩ := h.step2 hG hγa hθb hθv
  exact h'.typeA1 hG hθb' ((hb' μ).2 hμ) hμθ (Or.inl ((ha' γ).2 hγa)) hγv'

/-- **CCJS Lemma 2.4 (a), `d(b) < Δ`.** No colour missing at `a` or `b` is missing at `v`. -/
theorem IsK4.not_common_of_degree_b (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)}
    {a b u v : V} {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ)
    (hdeg : G.degree b < G.maxDegree) {θ : Fin G.maxDegree} (hθ : c.IsFree a θ ∨ c.IsFree b θ)
    (hθv : c.IsFree v θ) : False := by
  obtain ⟨μ, ν, hμν, hμ, hν⟩ := h.cm.two_free_right hdeg
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  rcases h.freeγ with hγa | hγb
  · rcases hθ with hθa | hθb
    · obtain ⟨c', hcm', hμa', hθb', hinv, -, hw, hcol, hflip, -, -⟩ :=
        h.cm.redistribute hG hθa hμ
      have hγθ : γ ≠ θ := fun he => h.not_free_v_γ (he ▸ hθv)
      have hγμ : γ ≠ μ := fun he => hdis γ hγa (he ▸ hμ)
      have hνθ : ν ≠ θ := fun he => hdis θ hθa (he ▸ hν)
      have hbu : ∃ δ', c'.col b u = some δ' ∧ c'.IsFree a δ' := by
        by_cases hδθ : δ = θ
        · subst hδθ
          exact ⟨μ, hflip u h.bu, hμa'⟩
        · have hδμ : δ ≠ μ := fun he => hdis δ h.freeδ (he ▸ hμ)
          exact ⟨δ, hcol b u δ h.bu hδθ hδμ, ((hinv δ hδθ hδμ).1).2 h.freeδ⟩
      obtain ⟨δ', hbu', hδ'⟩ := hbu
      have hγa' : c'.IsFree a γ := ((hinv γ hγθ hγμ).1).2 hγa
      have h' : IsK4 c' a b u v δ' γ :=
        ⟨hcm', hbu', hcol u v γ h.uv hγθ hγμ, hδ', Or.inl hγa', h.au, h.av, h.bv⟩
      exact h'.typeT0b hG hγa' hθb' ((hw v h.av.symm h.bv.symm θ).2 hθv)
        (((hinv ν hνθ hμν.symm).2).2 hν) hνθ
    · by_cases hμθ : μ = θ
      · exact h.typeT0b hG hγa hθb hθv hν (fun he => hμν (hμθ.trans he.symm))
      · exact h.typeT0b hG hγa hθb hθv hμ hμθ
  · by_cases hμγ : μ = γ
    · exact h.typeA1 hG hγb hν (fun he => hμν (hμγ.trans he.symm)) hθ hθv
    · exact h.typeA1 hG hγb hμ hμγ hθ hθv

/-- **CCJS Lemma 2.4 (a), `d(u) < Δ`** (via Kierstead's lemma). -/
theorem IsK4.not_common_of_degree_u (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)}
    {a b u v : V} {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ)
    (hdeg : G.degree u < G.maxDegree) {θ : Fin G.maxDegree} (hθ : c.IsFree a θ ∨ c.IsFree b θ)
    (hθv : c.IsFree v θ) : False := by
  let y : ℕ → V := fun i => if i = 0 then a else if i = 1 then b else if i = 2 then u else v
  have y0 : y 0 = a := rfl
  have y1 : y 1 = b := rfl
  have y2 : y 2 = u := rfl
  have y3 : y 3 = v := rfl
  have hab := h.ab
  have hau := h.au
  have hav := h.av
  have hbu := h.bu_ne
  have hbv := h.bv
  have huv := h.uv_ne
  have hK : IsKierstead c 4 y := by
    refine ⟨by omega, by rw [y0, y1]; exact h.cm.uncol, fun i hi => ?_, fun i hi j hj hij => ?_,
      fun i h1 hi => ?_⟩
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact h.cm.adj
      · exact h.adj_bu
      · exact h.adj_uv
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
        first
          | rfl
          | (rw [y0, y1] at hij; exact absurd hij hab)
          | (rw [y0, y2] at hij; exact absurd hij hau)
          | (rw [y0, y3] at hij; exact absurd hij hav)
          | (rw [y1, y0] at hij; exact absurd hij hab.symm)
          | (rw [y1, y2] at hij; exact absurd hij hbu)
          | (rw [y1, y3] at hij; exact absurd hij hbv)
          | (rw [y2, y0] at hij; exact absurd hij hau.symm)
          | (rw [y2, y1] at hij; exact absurd hij hbu.symm)
          | (rw [y2, y3] at hij; exact absurd hij huv)
          | (rw [y3, y0] at hij; exact absurd hij hav.symm)
          | (rw [y3, y1] at hij; exact absurd hij hbv.symm)
          | (rw [y3, y2] at hij; exact absurd hij huv.symm)
    · rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
      · exact ⟨0, by omega, δ, by rw [y1, y2]; exact h.bu, by rw [y0]; exact h.freeδ⟩
      · rcases h.freeγ with hγ | hγ
        · exact ⟨0, by omega, γ, by rw [y2, y3]; exact h.uv, by rw [y0]; exact hγ⟩
        · exact ⟨1, by omega, γ, by rw [y2, y3]; exact h.uv, by rw [y1]; exact hγ⟩
  have hd : ∀ m, 2 ≤ m → m + 1 < 4 → G.degree (y m) < G.maxDegree := by
    intro m h1 h2
    rcases (by omega : m = 2) with rfl
    rw [y2]
    exact hdeg
  have hcm : IsColMinus c (y 0) (y 1) := by rw [y0, y1]; exact h.cm
  have hE := kierstead_elementary hG 4 c y hcm hK hd
  rcases hθ with hθa | hθb
  · exact hE 0 3 (by omega) (by omega) θ (by rw [y0]; exact hθa) (by rw [y3]; exact hθv)
  · exact hE 1 3 (by omega) (by omega) θ (by rw [y1]; exact hθb) (by rw [y3]; exact hθv)

/-- **CCJS Lemma 2.4 (a).** If `d(b) < Δ` or `d(u) < Δ`, the Kierstead path `a b u v` is
elementary. -/
theorem IsK4.elementary (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u v : V}
    {δ γ : Fin G.maxDegree} (h : IsK4 c a b u v δ γ)
    (hdeg : G.degree b < G.maxDegree ∨ G.degree u < G.maxDegree) :
    Elementary c {a, b, u, v} := by
  obtain ⟨pab, -⟩ := h.cm.ab_facts hG
  obtain ⟨pau, pbu⟩ := fan_bau hG h.cm h.bu h.freeδ h.au
  have puv : ∀ θ, c.IsFree u θ → ¬ c.IsFree v θ := h.not_free_u_v hG
  have pv : ∀ θ, c.IsFree a θ ∨ c.IsFree b θ → ¬ c.IsFree v θ := fun θ hθ hθv => by
    rcases hdeg with hd | hd
    · exact h.not_common_of_degree_b hG hd hθ hθv
    · exact h.not_common_of_degree_u hG hd hθ hθv
  have pav : ∀ θ, c.IsFree a θ → ¬ c.IsFree v θ := fun θ hθ => pv θ (Or.inl hθ)
  have pbv : ∀ θ, c.IsFree b θ → ¬ c.IsFree v θ := fun θ hθ => pv θ (Or.inr hθ)
  intro x hx y hy hxy θ h1 h2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
      | exact hxy rfl
      | exact pab θ h1 h2 | exact pab θ h2 h1
      | exact pau θ h1 h2 | exact pau θ h2 h1
      | exact pbu θ h1 h2 | exact pbu θ h2 h1
      | exact puv θ h1 h2 | exact puv θ h2 h1
      | exact pav θ h1 h2 | exact pav θ h2 h1
      | exact pbv θ h1 h2 | exact pbv θ h2 h1

end Overfull
