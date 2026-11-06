/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Count.Wilson.LocalExact

/-!
# Optimal counting constant, part 7: the global seed (item 4)

A local seed `φ` on the copy `Fin m` of a piece (edge sums `τ`: `1/g` on reserve pairs, `1`
otherwise) is pushed to every piece `W_i` (`push`), and the pushes are summed over `i`.  An edge of
the residual host meeting a group lies in exactly one piece and gets `1`; a reserve pair lies in
all `g` pieces and gets `g · (1/g) = 1` (`global_seed`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Count.Wilson

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

section Push

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]

/-- Push-forward of triangle weights along an embedding. -/
def push (f : W ↪ V) (φ : Finset W → ℝ) (T : Finset V) : ℝ :=
  ∑ T' ∈ univ.filter (fun T' : Finset W => T'.map f = T), φ T'

theorem push_map (f : W ↪ V) (φ : Finset W → ℝ) (T' : Finset W) : push f φ (T'.map f) = φ T' := by
  unfold push
  rw [show univ.filter (fun T'' : Finset W => T''.map f = T'.map f) = {T'} by
    ext T''; simp [map_inj]]
  rw [sum_singleton]

theorem push_eq_zero (f : W ↪ V) (φ : Finset W → ℝ) {T : Finset V}
    (h : ∀ T' : Finset W, T'.map f ≠ T) : push f φ T = 0 := by
  unfold push
  rw [show univ.filter (fun T' : Finset W => T'.map f = T) = ∅ by
    ext T'; simp [h T']]
  rw [sum_empty]

theorem sum_push (f : W ↪ V) (φ : Finset W → ℝ) (A : Finset (Finset V)) :
    ∑ T ∈ A, push f φ T = ∑ T' ∈ univ.filter (fun T' : Finset W => T'.map f ∈ A), φ T' := by
  unfold push
  simp_rw [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun T' _ => ?_
  rw [sum_ite_eq]

theorem mem_triEdges_map_iff (f : W ↪ V) (T : Finset W) (x y : W) :
    s(f x, f y) ∈ triEdges (T.map f) ↔ s(x, y) ∈ triEdges T := by
  rw [mem_tE, mem_tE]
  simp [f.injective.eq_iff]

end Push

variable {a b c g t : ℕ} (h : WCond a b c g t) {S : Finset (Finset (Fin g))}

/-- The local vertex count. -/
abbrev mloc (a b c g t : ℕ) : ℕ := la a b c g t + lb a b c g t + lc a b c g t

theorem map_allowed (hS : _root_.STS.IsSTS S) (Λ : LFam S t) (i : Fin g)
    (T' : Finset (Fin (mloc a b c g t))) :
    IsAllowed (rHost (col3 a b c) (LX h Λ)) cdrF (T'.map (embV h i)) ↔
      T' ∈ tri (col3 (la a b c g t) (lb a b c g t) (lc a b c g t)) := by
  rw [mem_tri]
  have hcol : (T'.map (embV h i)).val.map (col3 a b c) =
      T'.val.map (col3 (la a b c g t) (lb a b c g t) (lc a b c g t)) := by
    rw [map_val, Multiset.map_map]
    congr 1
    funext j
    exact col3_embF h i j
  constructor
  · rintro ⟨h3, -, hF⟩
    refine ⟨by rwa [card_map] at h3, fun x _ y _ hxy => by simpa [cHost] using hxy, ?_⟩
    show T'.val.map _ ∈ cdrF
    rw [← hcol]; exact hF
  · rintro ⟨h3, -, hF⟩
    refine ⟨by rwa [card_map], fun x hx y hy hxy => ?_, ?_⟩
    · obtain ⟨j, -, rfl⟩ := mem_map.1 hx
      obtain ⟨k, -, rfl⟩ := mem_map.1 hy
      exact adj_of_InW h hS Λ (InW_embV h i j) (InW_embV h i k) hxy
    · show (T'.map (embV h i)).val.map (col3 a b c) ∈ cdrF
      rw [hcol]; exact hF

/-- The global seed. -/
def gseed (φ : Finset (Fin (mloc a b c g t)) → ℝ) (T : Finset (Fin (a + b + c))) : ℝ :=
  ∑ i : Fin g, push (embV h i) φ T

theorem push_bounds (hS : _root_.STS.IsSTS S) (Λ : LFam S t) {φ : Finset (Fin (mloc a b c g t)) → ℝ}
    {lo hi : ℝ} (hlo : 0 ≤ lo)
    (hφ : ∀ T ∈ tri (col3 (la a b c g t) (lb a b c g t) (lc a b c g t)), lo ≤ φ T ∧ φ T ≤ hi)
    (i : Fin g) {T : Finset (Fin (a + b + c))}
    (hT : IsAllowed (rHost (col3 a b c) (LX h Λ)) cdrF T) :
    0 ≤ push (embV h i) φ T ∧ push (embV h i) φ T ≤ max hi 0 := by
  by_cases hex : ∃ T' : Finset (Fin (mloc a b c g t)), T'.map (embV h i) = T
  · obtain ⟨T', rfl⟩ := hex
    rw [push_map]
    have := hφ T' ((map_allowed h hS Λ i T').1 hT)
    exact ⟨hlo.trans this.1, this.2.trans (le_max_left _ _)⟩
  · push Not at hex
    rw [push_eq_zero _ _ hex]
    exact ⟨le_rfl, le_max_right _ _⟩

/-- **The global seed is a diffuse seed of the residual host.** -/
theorem global_seed (hS : _root_.STS.IsSTS S) (Λ : LFam S t) (hg : 0 < g)
    {φ : Finset (Fin (mloc a b c g t)) → ℝ} {lo hi C : ℝ} (hlo : 0 ≤ lo)
    (hφ : ∀ T ∈ tri (col3 (la a b c g t) (lb a b c g t) (lc a b c g t)), lo ≤ φ T ∧ φ T ≤ hi)
    (hM : ∀ e : E0 (Fin (mloc a b c g t)),
      Minc (col3 (la a b c g t) (lb a b c g t) (lc a b c g t)) φ e = tau' g t e.1)
    (hC1 : 1 / (C * (a + b + c : ℕ)) ≤ lo) (hC2 : g * max hi 0 ≤ C / (a + b + c : ℕ)) :
    IsDiffuseSeed (rHost (col3 a b c) (LX h Λ)) cdrF C (gseed h φ) := by
  classical
  refine ⟨fun T hT => ?_, fun e he => ?_⟩
  · rw [Fintype.card_fin]
    obtain ⟨i0, hi0⟩ := exists_W h hS Λ hg hT
    -- `T` is the image of a local triangle in piece `i0`
    set T' := univ.filter fun j => embV h i0 j ∈ T
    have hTT : T'.map (embV h i0) = T := by
      ext v
      simp only [mem_map, T', mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact hj
      · intro hv
        obtain ⟨j, rfl⟩ := exists_embV h i0 (hi0 v hv)
        exact ⟨j, hv, rfl⟩
    have hb := fun i => push_bounds h hS Λ hlo hφ i hT
    constructor
    · calc 1 / (C * (a + b + c : ℕ)) ≤ lo := hC1
        _ ≤ push (embV h i0) φ T := by
            rw [← hTT, push_map]
            exact (hφ T' ((map_allowed h hS Λ i0 T').1 (hTT ▸ hT))).1
        _ ≤ gseed h φ T := by
            unfold gseed
            exact single_le_sum (fun i _ => (hb i).1) (mem_univ i0)
    · calc gseed h φ T ≤ ∑ _i : Fin g, max hi 0 := sum_le_sum fun i _ => (hb i).2
        _ = g * max hi 0 := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ C / (a + b + c : ℕ) := hC2
  · -- edge sums
    induction e using Sym2.ind with
    | _ u v =>
    have hadj : (rG (LX h Λ)).Adj u v := he
    have huv : u ≠ v := hadj.ne
    unfold gseed
    rw [sum_comm]
    -- the contribution of piece `i`
    have piece : ∀ i : Fin g, ∑ T ∈ (allowed (rHost (col3 a b c) (LX h Λ)) cdrF).filter
        (fun T => s(u, v) ∈ triEdges T), push (embV h i) φ T =
        if InW (g := g) (t := t) i.val u ∧ InW (g := g) (t := t) i.val v then
          (if InR g t u ∧ InR g t v then 1 / (g : ℝ) else 1) else 0 := by
      intro i
      rw [sum_push]
      split_ifs with hW hR hR
      · obtain ⟨j1, rfl⟩ := exists_embV h i hW.1
        obtain ⟨j2, rfl⟩ := exists_embV h i hW.2
        have hj : j1 ≠ j2 := fun e => huv (by rw [e])
        have := hM ⟨s(j1, j2), fun hd => hj (Sym2.mk_isDiag_iff.1 hd)⟩
        simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk] at this
        rw [tau'_mk, if_pos (by unfold IsRes; exact ⟨(InR_embV_iff h i j1).1 hR.1, (InR_embV_iff h i j2).1 hR.2⟩)] at this
        rw [← this]
        refine sum_congr ?_ fun _ _ => rfl
        ext T'
        simp only [mem_filter, mem_univ, true_and, mem_allowed_rHost, map_allowed h hS Λ i,
          mem_triEdges_map_iff]
      · obtain ⟨j1, rfl⟩ := exists_embV h i hW.1
        obtain ⟨j2, rfl⟩ := exists_embV h i hW.2
        have hj : j1 ≠ j2 := fun e => huv (by rw [e])
        have := hM ⟨s(j1, j2), fun hd => hj (Sym2.mk_isDiag_iff.1 hd)⟩
        simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk] at this
        rw [tau'_mk, if_neg (by unfold IsRes; rintro ⟨h1, h2⟩; exact hR ⟨(InR_embV_iff h i j1).2 h1, (InR_embV_iff h i j2).2 h2⟩)] at this
        rw [← this]
        refine sum_congr ?_ fun _ _ => rfl
        ext T'
        simp only [mem_filter, mem_univ, true_and, mem_allowed_rHost, map_allowed h hS Λ i,
          mem_triEdges_map_iff]
      · rw [sum_eq_zero]
        intro T' hT'
        exfalso
        simp only [mem_filter, mem_univ, true_and] at hT'
        obtain ⟨hu, hv, -⟩ := mem_tE.1 hT'.2
        obtain ⟨j1, -, rfl⟩ := mem_map.1 hu
        obtain ⟨j2, -, rfl⟩ := mem_map.1 hv
        exact hW ⟨InW_embV h i j1, InW_embV h i j2⟩
    refine (sum_congr rfl fun i _ => by convert piece i using 3).trans ?_
    by_cases hRR : InR g t u ∧ InR g t v
    · simp only [hRR, and_self, if_true]
      rw [sum_congr rfl fun i _ => if_pos ⟨Or.inr hRR.1, Or.inr hRR.2⟩]
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
      field_simp
    · rw [sum_congr rfl fun i _ => by rw [if_neg hRR]]
      -- exactly one piece contains both ends
      have hone : ∃ i0 : Fin g, ∀ i : Fin g,
          (InW (g := g) (t := t) i.val u ∧ InW (g := g) (t := t) i.val v) ↔ i = i0 := by
        have key : ∀ {p q : Fin (a + b + c)}, (rG (LX h Λ)).Adj p q → ¬ InR g t p →
            ∃ i0 : Fin g, ∀ i : Fin g,
              (InW (g := g) (t := t) i.val p ∧ InW (g := g) (t := t) i.val q) ↔ i = i0 := by
          intro p q hpq hpR
          obtain ⟨i0, hi0g, hp⟩ := InG_of_not_InR h.ht hpR
          refine ⟨⟨i0, hi0g⟩, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
          · rcases hi.1 with h1 | h1
            · exact Fin.ext (InG_unique h.ht h1 hp)
            · exact absurd h1 hpR
          · subst hi
            refine ⟨Or.inl hp, ?_⟩
            by_cases hqR : InR g t q
            · exact Or.inr hqR
            · obtain ⟨j, hj, hq⟩ := InG_of_not_InR h.ht hqR
              rw [adj_iff h hS] at hpq
              by_cases hij : i0 = j
              · subst hij; exact Or.inl hq
              · exact absurd ⟨⟨i0, hi0g⟩, ⟨j, hj⟩, fun e => hij (congrArg Fin.val e), hp, hq⟩ hpq.2
        by_cases huR : InR g t u
        · have hvR : ¬ InR g t v := fun hv => hRR ⟨huR, hv⟩
          obtain ⟨i0, hi0⟩ := key hadj.symm hvR
          exact ⟨i0, fun i => by rw [and_comm]; exact hi0 i⟩
        · exact key hadj huR
      obtain ⟨i0, hi0⟩ := hone
      rw [sum_congr rfl fun i _ => by rw [if_congr (hi0 i) rfl rfl]]
      rw [sum_ite_eq']
      simp

end CDRBicolour.Absorption.Count.Wilson
