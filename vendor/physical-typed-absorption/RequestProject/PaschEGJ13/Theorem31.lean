/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.Theorem31Main
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Theorem 3.1 of Ehard–Glock–Joos

Let `(V, <)` be a finite linearly ordered set and colour every `v ∈ V` independently and
uniformly at random with a colour `f(v) ∈ [q]`. For an `ℓ`-set `e = {v₁ < ⋯ < v_ℓ}` let
`f(e) = (f(v₁), …, f(v_ℓ))`, fix a pattern `α ∈ [q]^ℓ` and let `E_α` be the random set of all
`ℓ`-sets `e` with `f(e) = α`. For an `ℓ`-tuple weight function `ω` (a weight function on
`ℓ`-subsets of `V`) let `‖ω‖_k = max_{|T| = k} ω(T)` with `ω(T) = ∑_{S ⊇ T} ω(S)`, and
`M = q^{-ℓ} max_{k ∈ [ℓ]} ‖ω‖_k q^k g^{k-1}`.

**Theorem 3.1.** If `g ≥ 24 ℓ³ (ℓ + 1 + log |V|)`, then for every `λ > 0`
`P[|ω(E_α) - E ω(E_α)| ≥ λ] ≤ 2^ℓ exp(-λ² / (12 ℓ² M (λ + E ω(E_α)))) + exp(-g / (24 ℓ²))`.

Formalization choices:
* The colouring is `f : V → Fin q`, distributed according to the uniform product measure
  `unif V q`; probabilities and expectations are the finite sums `pProb`, `pE`.
* `f(e) = α` is `HasPattern f α e`: `|e| = ℓ` and the `i`-th smallest element of `e` (given by
  `Finset.orderEmbOfFin`) has colour `α i`.
* The weight function `ω : Finset V → ℝ` only needs to be nonnegative on `ℓ`-sets; its values
  on other sets are irrelevant.
* `‖ω‖_k` is `tupleNorm ℓ ω k` (a supremum over the finitely many `k`-sets), and `M` is
  `thm31M q ℓ g ω`. We assume `ℓ ≥ 1` and `q ≥ 1` (needed for the statement to make sense).
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- `f(e) = α`: `e` is an `ℓ`-set whose `i`-th smallest element has colour `α i`. -/
def HasPattern {q ℓ : ℕ} (f : V → Fin q) (α : Fin ℓ → Fin q) (e : Finset V) : Prop :=
  ∃ h : e.card = ℓ, ∀ i, f (e.orderEmbOfFin h i) = α i

open Classical in
/-- The random variable `ω(E_α)`. -/
noncomputable def patWeight {q : ℕ} (ℓ : ℕ) (ω : Finset V → ℝ) (α : Fin ℓ → Fin q)
    (f : V → Fin q) : ℝ :=
  ∑ e ∈ powersetCard ℓ univ, ω e * if HasPattern f α e then 1 else 0

/-- `ω(T) = ∑_{S ⊇ T} ω(S)`, the sum over the `ℓ`-sets `S` containing `T`. -/
noncomputable def tupleDeg (ℓ : ℕ) (ω : Finset V → ℝ) (T : Finset V) : ℝ :=
  ∑ S ∈ (powersetCard ℓ univ).filter (fun S => T ⊆ S), ω S

/-- `‖ω‖_k = max_{|T| = k} ω(T)`. -/
noncomputable def tupleNorm (ℓ : ℕ) (ω : Finset V → ℝ) (k : ℕ) : ℝ :=
  ⨆ T : {T : Finset V // T.card = k}, tupleDeg ℓ ω T

/-- `M = q^{-ℓ} max_{k ∈ [ℓ]} ‖ω‖_k q^k g^{k-1}`. -/
noncomputable def thm31M (q ℓ : ℕ) (g : ℝ) (ω : Finset V → ℝ) : ℝ :=
  (⨆ k : Fin ℓ, tupleNorm ℓ ω (k + 1) * (q : ℝ) ^ ((k : ℕ) + 1) * g ^ (k : ℕ)) / (q : ℝ) ^ ℓ

/-- The rank of the `i`-th smallest element of `e` is `i`. -/
theorem card_filter_lt_orderEmbOfFin (e : Finset V) {ℓ : ℕ} (h : e.card = ℓ) (i : Fin ℓ) :
    (e.filter (· < e.orderEmbOfFin h i)).card = i := by
  have : e.filter (· < e.orderEmbOfFin h i) =
      (univ.filter (fun j : Fin ℓ => j < i)).map (e.orderEmbOfFin h).toEmbedding := by
    ext y
    simp only [mem_filter, mem_map, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hy, hyi⟩
      have : y ∈ Set.range (e.orderEmbOfFin h) := by rw [range_orderEmbOfFin]; exact hy
      obtain ⟨j, rfl⟩ := this
      exact ⟨j, (e.orderEmbOfFin h).lt_iff_lt.mp hyi, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨orderEmbOfFin_mem e h j, (e.orderEmbOfFin h).lt_iff_lt.mpr hj⟩
  rw [this, card_map]
  have : univ.filter (fun j : Fin ℓ => j < i) = Iio i := by ext j; simp
  rw [this, Fin.card_Iio]

/-- `f(e) = α` in terms of ranks. -/
theorem hasPattern_iff {q ℓ : ℕ} (hq : 0 < q) (f : V → Fin q) (α : Fin ℓ → Fin q)
    (e : Finset V) (he : e.card = ℓ) :
    HasPattern f α e ↔ ∀ v ∈ e, f v =
      (fun i : ℕ => if h : i < ℓ then α ⟨i, h⟩ else (⟨0, hq⟩ : Fin q))
        ((e.filter (· < v)).card) := by
  constructor
  · rintro ⟨h, H⟩ v hv
    have : v ∈ Set.range (e.orderEmbOfFin h) := by rw [range_orderEmbOfFin]; exact hv
    obtain ⟨i, rfl⟩ := this
    simp only [card_filter_lt_orderEmbOfFin, i.2, dif_pos]
    exact H i
  · intro H
    refine ⟨he, fun i => ?_⟩
    have := H _ (orderEmbOfFin_mem e he i)
    simpa [card_filter_lt_orderEmbOfFin, i.2] using this

variable [DecidableEq V]

/-- **Theorem 3.1** (Ehard–Glock–Joos). -/
theorem theorem_3_1 (q ℓ : ℕ) (hq : 0 < q) (hℓ : 1 ≤ ℓ) (α : Fin ℓ → Fin q)
    (ω : Finset V → ℝ) (hω : ∀ e : Finset V, e.card = ℓ → 0 ≤ ω e) (g : ℝ)
    (hg : 24 * (ℓ : ℝ) ^ 3 * (ℓ + 1 + Real.log (Fintype.card V)) ≤ g) (lam : ℝ)
    (hlam : 0 < lam) :
    pProb (unif V q) (fun f => lam ≤ |patWeight ℓ ω α f - pE (unif V q) (patWeight ℓ ω α)|) ≤
      2 ^ ℓ * Real.exp (-(lam ^ 2 / (12 * ℓ ^ 2 * thm31M q ℓ g ω *
        (lam + pE (unif V q) (patWeight ℓ ω α))))) +
      Real.exp (-(g / (24 * ℓ ^ 2))) := by
  classical
  set n := Fintype.card V with hn
  set eiso : Fin n ≃o V := Fintype.orderIsoFinOfCardEq V rfl with heiso
  set emb : Fin n ↪ V := eiso.toEquiv.toEmbedding with hemb
  set e : V ≃ Fin n := eiso.symm.toEquiv with he
  set α' : ℕ → Fin q := fun i => if h : i < ℓ then α ⟨i, h⟩ else (⟨0, hq⟩ : Fin q) with hα'
  set w : Finset (Fin n) → ℝ := fun T => if T.card = ℓ then ω (T.map emb) else 0 with hw
  have hw0 : ∀ T, 0 ≤ w T := by
    intro T; simp only [hw]; split_ifs with h
    · exact hω _ (by rw [card_map, h])
    · exact le_rfl
  -- transport of sums over `ℓ`-sets
  have hsum : ∀ F : Finset V → ℝ, ∑ T ∈ powersetCard ℓ (univ : Finset (Fin n)), F (T.map emb) =
      ∑ S ∈ powersetCard ℓ (univ : Finset V), F S := by
    intro F
    refine sum_nbij' (fun T => T.map emb) (fun S => S.map e.toEmbedding) ?_ ?_ ?_ ?_ ?_
    · intro T hT; simp only [mem_powersetCard] at hT ⊢; exact ⟨subset_univ _, by
        rw [card_map, hT.2]⟩
    · intro S hS; simp only [mem_powersetCard] at hS ⊢; exact ⟨subset_univ _, by
        rw [card_map, hS.2]⟩
    · intro T _; ext x; simp [hemb, he]
    · intro S _; ext x; simp [hemb, he]
    · intro T _; rfl
  have hrank : ∀ (T : Finset (Fin n)) (t : Fin n),
      ((T.map emb).filter (· < emb t)).card = (T.filter (· < t)).card := by
    intro T t
    rw [← card_map emb]
    congr 1
    ext y
    simp only [mem_filter, mem_map, hemb, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hlt⟩
      exact ⟨a, ⟨ha, eiso.lt_iff_lt.mp hlt⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hlt⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, eiso.lt_iff_lt.mpr hlt⟩
  have hpat : ∀ (c : Fin n → Fin q) (T : Finset (Fin n)), T.card = ℓ →
      (HasPattern (c ∘ e) α (T.map emb) ↔ Patt.Pat α' c T) := by
    intro c T hT
    rw [hasPattern_iff hq _ α _ (by rw [card_map, hT])]
    unfold Patt.Pat Patt.rk
    constructor
    · intro H t ht
      have := H (emb t) (mem_map_of_mem emb ht)
      rw [hrank] at this
      simpa [he, hemb] using this
    · intro H v hv
      rw [mem_map] at hv
      obtain ⟨t, ht, rfl⟩ := hv
      rw [hrank]
      simpa [he, hemb] using H t ht
  have hcnt : ∀ c : Fin n → Fin q, patWeight ℓ ω α (c ∘ e) = Patt.cnt ℓ w α' c := by
    intro c
    unfold patWeight Patt.cnt
    rw [← hsum]
    refine sum_congr rfl fun T hT => ?_
    rw [mem_powersetCard] at hT
    simp only [hw, if_pos hT.2]
    congr 2
    exact propext (hpat c T hT.2)
  have hunif : (fun j => unif V q (e.symm j)) = unif (Fin n) q := rfl
  have hE : pE (unif V q) (patWeight ℓ ω α) = Patt.nrm ℓ w ∅ * (1 / (q : ℝ)) ^ ℓ := by
    rw [pE_equiv e, hunif]
    simp_rw [hcnt]
    rw [Patt.pE_cnt hq, Patt.nrm_empty_eq, sum_mul]
  -- the norm bound
  have hg0 : 0 < g := by
    have : 0 ≤ Real.log (Fintype.card V) := Real.log_natCast_nonneg _
    have : 0 < 24 * (ℓ : ℝ) ^ 3 * (ℓ + 1 + Real.log (Fintype.card V)) := by positivity
    linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hNB : Patt.NB ℓ w q g (thm31M q ℓ g ω) := by
    intro j hj1 hjl T hT
    have h1 : Patt.nrm ℓ w T = tupleDeg ℓ ω (T.map emb) := by
      unfold Patt.nrm tupleDeg
      rw [sum_filter, sum_filter, ← hsum]
      refine sum_congr rfl fun T' hT' => ?_
      rw [mem_powersetCard] at hT'
      simp only [hw, if_pos hT'.2, map_subset_map]
    have h2 : tupleDeg ℓ ω (T.map emb) ≤ tupleNorm ℓ ω j := by
      unfold tupleNorm
      refine le_ciSup_of_le (Set.finite_range _).bddAbove ⟨T.map emb, by rw [card_map, hT]⟩
        le_rfl
    have h3 : tupleNorm ℓ ω j * (q : ℝ) ^ j * g ^ (j - 1) ≤
        ⨆ k : Fin ℓ, tupleNorm ℓ ω (k + 1) * (q : ℝ) ^ ((k : ℕ) + 1) * g ^ (k : ℕ) := by
      have := le_ciSup (Set.finite_range (fun k : Fin ℓ => tupleNorm ℓ ω (k + 1) *
        (q : ℝ) ^ ((k : ℕ) + 1) * g ^ (k : ℕ))).bddAbove ⟨j - 1, by omega⟩
      simp only at this
      have hj : j - 1 + 1 = j := by omega
      rw [hj] at this
      exact this
    unfold thm31M
    rw [h1]
    apply div_le_div_of_nonneg_right _ (by positivity)
    refine le_trans ?_ h3
    gcongr
  -- apply Theorem 3.1 on `Fin n`
  have hmain := Patt.conc31 (n := n) hq ℓ hℓ hg w hw0 α' (thm31M q ℓ g ω) hNB lam hlam
  rw [hE, pProb_equiv e, hunif]
  simp_rw [hcnt]
  exact hmain

end Pseudorandom
