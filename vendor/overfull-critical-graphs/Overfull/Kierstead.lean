/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Linkage

/-!
# Kierstead paths (Kierstead 1984, Lemma 2; Zhang 2000)

A *Kierstead path* `y₀ y₁ … y_{L−1}` for a colouring `c` of `G − y₀y₁` is a path of distinct
vertices in which the colour of every edge `yᵢ yᵢ₊₁`, `i ≥ 1`, is missing at some earlier
`yⱼ`, `j < i` (`IsKierstead`).

`kierstead_elementary` (H. A. Kierstead, *On the chromatic index of multigraphs without large
triangles*, JCTB 36 (1984), Lemma 2, adapted to `Δ` colours as observed by L. Zhang, Graphs
Combin. 16 (2000)): in a class-two graph, if every interior vertex `yₘ`, `2 ≤ m ≤ L − 2`, has
degree less than `Δ`, the vertex set of a Kierstead path is elementary. The proof is Kierstead's
double induction (on the length, then on the distance between two vertices sharing a missing
colour), with `(θ, δ)`-Kempe swaps.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A Kierstead path of length `L` (vertices `y 0, …, y (L − 1)`) for the uncoloured edge
`y₀ y₁`. -/
structure IsKierstead {k : ℕ} (c : PEC G (Fin k)) (L : ℕ) (y : ℕ → V) : Prop where
  two : 2 ≤ L
  uncol : c.col (y 0) (y 1) = none
  adj : ∀ i, i + 1 < L → G.Adj (y i) (y (i + 1))
  inj : ∀ i < L, ∀ j < L, y i = y j → i = j
  step : ∀ i, 1 ≤ i → i + 1 < L →
    ∃ j < i, ∃ γ, c.col (y i) (y (i + 1)) = some γ ∧ c.IsFree (y j) γ

theorem IsKierstead.prefix {k : ℕ} {c : PEC G (Fin k)} {L m : ℕ} {y : ℕ → V}
    (hK : IsKierstead c L y) (hm : m ≤ L) (h2 : 2 ≤ m) : IsKierstead c m y :=
  ⟨h2, hK.uncol, fun i hi => hK.adj i (by omega),
    fun i hi j hj h => hK.inj i (by omega) j (by omega) h,
    fun i h1 hi => hK.step i h1 (by omega)⟩

theorem IsColMinus.symm {k : ℕ} {c : PEC G (Fin k)} {a b : V} (hcm : IsColMinus c a b) :
    IsColMinus c b a :=
  ⟨hcm.adj.symm, by rw [c.col_symm]; exact hcm.uncol,
    fun u v huv hne => hcm.total u v huv (fun h => hne (h.trans Sym2.eq_swap))⟩

theorem IsColMinus.exists_free_right {c : PEC G (Fin G.maxDegree)} {a b : V}
    (hcm : IsColMinus c a b) : ∃ γ, c.IsFree b γ :=
  hcm.symm.exists_free_left

/-- A vertex of degree below `Δ` misses some colour. -/
theorem exists_free_of_degree_lt (c : PEC G (Fin G.maxDegree)) {v : V}
    (h : G.degree v < G.maxDegree) : ∃ γ, c.IsFree v γ := by
  have h1 := card_missing_add_colNbrs c v
  have h2 : #(colNbrs c v) ≤ G.degree v := by
    rw [← card_neighborFinset_eq_degree]
    classical
    exact card_le_card (filter_subset _ _)
  obtain ⟨γ, hγ⟩ : (missing c v).Nonempty := by
    rw [← card_pos]
    omega
  exact ⟨γ, mem_missing.1 hγ⟩

/-- After recolouring the edge `u v` with a colour free at both ends, its old colour is free at
`u`. -/
theorem isFree_setEdge_old {k : ℕ} (c : PEC G (Fin k)) {u v : V} (θ : Fin k) (hadj : G.Adj u v)
    (hu : c.IsFree u θ) (hv : c.IsFree v θ) {γ : Fin k} (hγ : c.col u v = some γ) :
    (c.setEdge θ hadj hu hv).IsFree u γ := by
  intro w hw
  by_cases hwv : w = v
  · subst hwv
    rw [setEdge_col, updFun_left] at hw
    have : θ = γ := Option.some_injective _ hw
    subst this
    exact hu w hγ
  · rw [setEdge_col, updFun_of_ne] at hw
    · exact hwv (c.col_proper hw hγ)
    · rintro (⟨-, h⟩ | ⟨rfl, rfl⟩)
      · exact hwv h
      · exact hadj.ne rfl

/-- The `(θ, δ)`-swap at `w` does not touch the uncoloured edge. -/
theorem kempeSwap_col_none {k : ℕ} (c : PEC G (Fin k)) (θ δ : Fin k) (w : V) {u v : V}
    (h : c.col u v = none) : (c.kempeSwap θ δ w).col u v = none := by
  simp only [kempeSwap_col, kempeSwapFun]
  split_ifs <;> simp [h]

/-- **Kierstead's lemma** (Kierstead 1984, Lemma 2; Zhang 2000). In a class-two graph, the vertex
set of a Kierstead path whose interior vertices `y₂, …, y_{L−2}` have degree less than `Δ` is
elementary. -/
theorem kierstead_elementary (hG : IsClassTwo G) :
    ∀ (L : ℕ) (c : PEC G (Fin G.maxDegree)) (y : ℕ → V), IsColMinus c (y 0) (y 1) →
      IsKierstead c L y → (∀ m, 2 ≤ m → m + 1 < L → G.degree (y m) < G.maxDegree) →
      ∀ i j, i < j → j < L → ∀ θ, c.IsFree (y i) θ → ¬ c.IsFree (y j) θ := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro c y hcm hK hdeg i j hij hj θ hθi hθj
    by_cases hjL : j + 1 < L
    · exact ih (j + 1) (by omega) c y hcm (hK.prefix (by omega) (by omega))
        (fun m h2 hm => hdeg m h2 (by omega)) i j hij (by omega) θ hθi hθj
    have hjeq : j = L - 1 := by omega
    subst hjeq
    -- secondary induction on the distance `L − 1 − i`, over all colourings
    suffices H : ∀ d (c : PEC G (Fin G.maxDegree)) i, IsColMinus c (y 0) (y 1) →
        IsKierstead c L y → L - 1 - i = d → i < L - 1 → ∀ θ, c.IsFree (y i) θ →
        c.IsFree (y (L - 1)) θ → False from H _ c i hcm hK rfl hij θ hθi hθj
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ihd =>
      intro c i hcm hK hd hi θ hθi hθj
      -- the prefix `y₀ … y_{L−2}` is elementary (primary induction)
      have hpre : ∀ a b, a < b → b < L - 1 → ∀ γ, c.IsFree (y a) γ → ¬ c.IsFree (y b) γ := by
        intro a b hab hb γ
        exact ih (L - 1) (by omega) c y hcm (hK.prefix (by omega) (by omega))
          (fun m h2 hm => hdeg m h2 (by omega)) a b hab hb γ
      have huniq : ∀ a b, a < L - 1 → b < L - 1 → ∀ γ, c.IsFree (y a) γ → c.IsFree (y b) γ →
          a = b := by
        intro a b ha hb γ h1 h2
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · exact hpre a b h hb γ h1 h2
        · exact hpre b a h ha γ h2 h1
      by_cases hadjc : i + 2 = L
      · -- adjacent vertices `y_{L−2}, y_{L−1}`
        have hiL : i + 1 = L - 1 := by omega
        rw [← hiL] at hθj
        by_cases hi0 : i = 0
        · subst hi0
          refine not_total_of_classTwo hG (c.setEdge θ hcm.adj hθi hθj) fun u v huv => ?_
          by_cases h : s(u, v) = s(y 0, y 1)
          · rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · simp
            · rw [PEC.col_symm]; simp
          · exact extends_setEdge c θ hcm.adj hθi hθj u v (hcm.total u v huv h)
        · obtain ⟨m, hmi, γ, hγ, hγm⟩ := hK.step i (by omega) (by omega)
          have hadj := hK.adj i (by omega)
          set c' := c.setEdge θ hadj hθi hθj
          have hne0 : ∀ a b, a + 1 ≤ i → ¬ ((y a = y i ∧ y b = y (i + 1)) ∨
              (y a = y (i + 1) ∧ y b = y i)) := by
            intro a b ha h
            rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
            · have := hK.inj a (by omega) i (by omega) h1; omega
            · have := hK.inj a (by omega) (i + 1) (by omega) h1; omega
          have hcm' : IsColMinus c' (y 0) (y 1) := by
            refine ⟨hcm.adj, ?_, fun u v huv hne => extends_setEdge c θ hadj hθi hθj u v
              (hcm.total u v huv hne)⟩
            show updFun c.col (y i) (y (i + 1)) (some θ) (y 0) (y 1) = none
            rw [updFun_of_ne _ (hne0 0 1 (by omega)), hcm.uncol]
          have hK' : IsKierstead c' (i + 1) y := by
            refine ⟨by omega, hcm'.uncol, fun a ha => hK.adj a (by omega),
              fun a ha b hb h => hK.inj a (by omega) b (by omega) h, fun a h1 ha => ?_⟩
            obtain ⟨b, hb, δ, hδ, hδf⟩ := hK.step a h1 (by omega)
            refine ⟨b, hb, δ, ?_, ?_⟩
            · show updFun c.col (y i) (y (i + 1)) (some θ) (y a) (y (a + 1)) = some δ
              rw [updFun_of_ne _ (hne0 a (a + 1) (by omega)), hδ]
            · rw [isFree_setEdge_of_ne c θ hadj hθi hθj
                (fun h => by have := hK.inj b (by omega) i (by omega) h; omega)
                (fun h => by have := hK.inj b (by omega) (i + 1) (by omega) h; omega)]
              exact hδf
          refine ih (i + 1) (by omega) c' y hcm' hK' (fun m h2 hm => hdeg m h2 (by omega))
            m i hmi (by omega) γ ?_ (isFree_setEdge_old c θ hadj hθi hθj hγ)
          rw [isFree_setEdge_of_ne c θ hadj hθi hθj
            (fun h => by have := hK.inj m (by omega) i (by omega) h; omega)
            (fun h => by have := hK.inj m (by omega) (i + 1) (by omega) h; omega)]
          exact hγm
      · -- `i + 2 < L`: a colour `δ` missing at `y_{i+1}`
        have hδex : ∃ δ, c.IsFree (y (i + 1)) δ := by
          by_cases h1 : i + 1 = 1
          · rw [h1]; exact hcm.exists_free_right
          · exact exists_free_of_degree_lt c (hdeg (i + 1) (by omega) (by omega))
        obtain ⟨δ, hδ⟩ := hδex
        have hδθ : δ ≠ θ := fun h => hpre i (i + 1) (by omega) (by omega) θ hθi (h ▸ hδ)
        set K := c.kempeGraph θ δ
        set w := y (i + 1)
        set c' := c.kempeSwap θ δ w
        have hcm' : IsColMinus c' (y 0) (y 1) :=
          ⟨hcm.adj, kempeSwap_col_none c θ δ w hcm.uncol,
            fun u v huv hne => extends_kempeSwap c θ δ w u v (hcm.total u v huv hne)⟩
        have hθw : c'.IsFree w θ := by
          rw [isFree_kempeSwap_of_reachable c θ δ (Reachable.refl _), Equiv.swap_apply_left]
          exact hδ
        by_cases hr : K.Reachable w (y i)
        · -- the chain ends at `y_i`: the whole path stays a Kierstead path
          have hθi' : c'.IsFree (y i) δ := by
            rw [isFree_kempeSwap_of_reachable c θ δ hr, Equiv.swap_apply_right]
            exact hθi
          have hlast : ¬ K.Reachable w (y (L - 1)) := by
            intro h
            exact not_three_linked c (u := w) (v := y i) (w := y (L - 1))
              (fun h' => by have := hK.inj (i + 1) (by omega) i (by omega) h'; omega)
              (fun h' => by have := hK.inj (i + 1) (by omega) (L - 1) (by omega) h'; omega)
              (fun h' => by have := hK.inj i (by omega) (L - 1) (by omega) h'; omega)
              (Or.inr hδ) (Or.inl hθi) (Or.inl hθj) hr h
          have hK' : IsKierstead c' L y := by
            refine ⟨hK.two, hcm'.uncol, hK.adj, hK.inj, fun m h1 hm => ?_⟩
            obtain ⟨l, hl, γ, hγ, hγf⟩ := hK.step m h1 hm
            by_cases hγθ : γ = θ
            · subst hγθ
              have hli : l = i := huniq l i (by omega) (by omega) _ hγf hθi
              subst hli
              by_cases hym : K.Reachable w (y m)
              · refine ⟨l, hl, δ, ?_, hθi'⟩
                rw [kempeSwap_col, kempeSwapFun_of_reachable c _ δ hym, hγ]
                simp
              · have hm1 : l + 1 < m := by
                  rcases Nat.lt_or_ge (l + 1) m with h | h
                  · exact h
                  · exact absurd (by have : m = l + 1 := by omega
                                     rw [this]) hym
                refine ⟨l + 1, hm1, γ, ?_, hθw⟩
                rw [kempeSwap_col, kempeSwapFun_of_not_reachable c γ δ hym, hγ]
            · by_cases hγδ : γ = δ
              · subst hγδ
                have hli : l = i + 1 := huniq l (i + 1) (by omega) (by omega) _ hγf hδ
                subst hli
                by_cases hym : K.Reachable w (y m)
                · refine ⟨i + 1, hl, θ, ?_, hθw⟩
                  rw [kempeSwap_col, kempeSwapFun_of_reachable c θ γ hym, hγ]
                  simp
                · refine ⟨i, by omega, γ, ?_, hθi'⟩
                  rw [kempeSwap_col, kempeSwapFun_of_not_reachable c θ γ hym, hγ]
              · exact ⟨l, hl, γ, kempeSwap_col_of_ne c θ δ w _ _ hγ hγθ hγδ,
                  (kempeSwap_isFree_of_ne c θ δ w _ hγθ hγδ).2 hγf⟩
          refine ihd (L - 1 - (i + 1)) (by omega) c' (i + 1) hcm' hK' rfl (by omega) θ hθw ?_
          rw [isFree_kempeSwap_of_not_reachable c θ δ hlast]
          exact hθj
        · -- the chain avoids `y_i`: the prefix up to `y_{i+1}` stays a Kierstead path
          have hK' : IsKierstead c' (i + 2) y := by
            refine ⟨by omega, hcm'.uncol, fun a ha => hK.adj a (by omega),
              fun a ha b hb h => hK.inj a (by omega) b (by omega) h, fun m h1 hm => ?_⟩
            obtain ⟨l, hl, γ, hγ, hγf⟩ := hK.step m h1 (by omega)
            have hγθ : γ ≠ θ := fun h => by
              have := huniq l i (by omega) (by omega) γ hγf (h ▸ hθi); omega
            have hγδ : γ ≠ δ := fun h => by
              have := huniq l (i + 1) (by omega) (by omega) γ hγf (h ▸ hδ); omega
            exact ⟨l, hl, γ, kempeSwap_col_of_ne c θ δ w _ _ hγ hγθ hγδ,
              (kempeSwap_isFree_of_ne c θ δ w _ hγθ hγδ).2 hγf⟩
          refine ih (i + 2) (by omega) c' y hcm' hK' (fun m h2 hm => hdeg m h2 (by omega))
            i (i + 1) (by omega) (by omega) θ ?_ hθw
          rw [isFree_kempeSwap_of_not_reachable c θ δ hr]
          exact hθi

end Overfull
