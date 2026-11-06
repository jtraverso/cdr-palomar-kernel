/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V48.CoreExt
public import RequestProject.S07V48.SeedPersist
public import RequestProject.S07V45.CoreSpecialize
@[expose] public section

/-!
# V48 — ONE sampled core carrying the V25 package AND the raw fractional-seed profile

* `thetaSeed C q δ = (min δ 1)² q² / (4C)` — the rate of the weighted tests (constants only).
* `S07_core_seed_H3H4` — constants `t, a, ε, n₀` from `(α, q, h, C, δ)` BEFORE the host. For every
  host with the ORIGINAL `CommonNbrCond` (H3), `HingeCond` (H4), `n ≥ n₀`, and EVERY original
  exact diffuse seed `φ` (`DiffuseSeed G lab F C φ`), there is ONE `W` with all five V25
  conclusions (size, pools, hinges, robust routes for every later `Z`, `B`) AND, for every host
  edge `uv` (roots inside or outside `W`), `|(∑_{a ∈ W} compW … u v a) / q - 1| ≤ δ`.
  The weighted tests are intersected into the SAME union bound as the V25 tests
  (`S07_core_ext`); no existential core theorem is applied twice.
* `CoreItems` — the V45 items 1–3 for a set `W`, as one transparent proposition;
  `coreItems_of_contract` — they follow from `CorePathContract` (V45 lemmas, unchanged).
-/

open Finset

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace S07V48

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V24 S07V25 S07V45

/-- the rate of the weighted completion tests (depends only on the constants) -/
def thetaSeed (C q δ : ℝ) : ℝ := (min δ 1) ^ 2 * q ^ 2 / (4 * C)

open Classical in
/-- **ONE core: V25 package + raw fractional-seed profile on every host edge** -/
theorem S07_core_seed_H3H4 (α q C δ : ℝ) (h : ℕ) (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 6 ≤ h) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ (t : ℕ) (a ε : ℝ) (n₀ : ℕ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)) (_ : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h),
        n₀ ≤ Fintype.card V →
        ∀ φ : Finset V → ℝ, DiffuseSeed G lab F C φ →
          ∃ W : Finset V,
            q * Fintype.card V / 2 ≤ W.card ∧ (W.card : ℝ) < 2 * q * Fintype.card V ∧
            (∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
              q * α * Fintype.card V / 2 ≤ ((commonNbrs G lab k u v) ∩ W).card) ∧
            (∀ u v a' b' : V, HingeTest G lab F u v a' b' →
              α * q ^ (hOrd hH4 u v a' b' - 4) *
                  (Fintype.card V : ℝ) ^ (hOrd hH4 u v a' b' - 4) / 2 ≤
                ((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
                  freeV u v a' b' J ⊆ W).card) ∧
            (∀ (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ),
              (Z.card : ℝ) ≤ ε * Fintype.card V → (∀ u, B.degree u ≤ d) →
              (d : ℝ) ≤ ε * Fintype.card V →
              ∀ v x y, AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C))
                  (colG G lab F) v x y →
                ∃ p ∈ pathsLen (link G lab F v) t x y, intlSet (t - 1) p ⊆ W ∧
                  (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z) ∧
                  ∀ k < t, ¬ B.Adj (p.getVert k) (p.getVert (k + 1))) ∧
            ∀ u v : V, G.Adj u v → |sampW G lab F φ W u v / q - 1| ≤ δ := by
  set δ' := min δ 1 with hδ'def
  have hδ' : 0 < δ' := lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hθ : 0 < thetaSeed C q δ := by unfold thetaSeed; positivity
  obtain ⟨t, a, ε, n₀, ht, ht3, ha, hε, hmain⟩ := S07_core_ext α q (thetaSeed C q δ) h hα hq hq1
    hh hθ
  refine ⟨t, a, ε, max n₀ 1, ht, ht3, ha, hε, ?_⟩
  intro V _ _ I G lab F hH3 hH4 hn φ hφ
  have hn0 : 0 < Fintype.card V := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hn)
  have hcard : Fintype.card (V × V × Bool) ≤ 2 * Fintype.card V ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_bool]; nlinarith
  obtain ⟨W, h1, h2, h3, h4, h5, h6⟩ := hmain V I G lab F hH3 hH4 (le_trans (le_max_left _ _) hn)
    (V × V × Bool) hcard (seedBad G lab F φ q δ') (fun j => by
      have := seedBad_prob hφ hC hq hq1 hδ' hδ'1 hn0 j
      simpa only [thetaSeed, ← hδ'def] using this)
  exact ⟨W, h1, h2, h3, h4, h5, fun u v huv => (profile_of_not_bad hq h6 huv).trans hδ'δ⟩

/-- the V45 items 1–3 for a set `W` (transparent conjunction of the V45 conclusions) -/
def CoreItems {V I : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (lab : V → I)
    (F : Set (Multiset I)) (W : Finset V) : Prop :=
  (∀ v ∈ W, activeComps (indG G W) lab F v =
    ((activeComps G lab F v).filter (fun C => (C ∩ W).Nonempty)).image (· ∩ W)) ∧
  (∀ v ∈ W, ∀ C ∈ activeComps G lab F v, ∀ x ∈ C, x ∈ W →
    comp (indG G W) lab F v x = C ∩ W) ∧
  (∀ v ∈ W, ∀ C ∈ activeComps G lab F v, ∀ x ∈ C, x ∈ W →
    (IsBip (indG G W) lab F (v, C ∩ W) ↔ IsBip G lab F (v, C)) ∧
    (IsBip G lab F (v, C) → ∃ s : Bool, ∀ u ∈ C ∩ W,
      col (indG G W) lab F (v, C ∩ W) u = xor s (col G lab F (v, C) u))) ∧
  (∀ x : Sym2 V → ℤ, x ∈ localProfile G lab F → x ∈ CoreSupp G W →
    x ∈ MCore G lab F W ∧
    IsLocalProfile (G.comap (Subtype.val : {a // a ∈ W} → V)) (lab ∘ Subtype.val) F
      (toCore W x) ∧
    liftE (ι := (Subtype.val : {a // a ∈ W} → V)) (toCore W x) = x ∧
    l1E (toCore W x) = l1E x)

/-- the V45 items follow from the transparent contract (V45 lemmas, unchanged) -/
theorem coreItems_of_contract {V I : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {lab : V → I} {F : Set (Multiset I)} {W : Finset V} {t : ℕ}
    (hCt : CorePathContract G lab F W t) (ht : Odd t) (ht3 : 3 ≤ t) :
    CoreItems G lab F W :=
  ⟨fun v hv => by convert activeComps_core hCt ht3 hv,
    fun v hv C hC x hx hxW => by convert core_comp_eq hCt ht3 hv hC hx hxW,
    fun v hv C hC x hx hxW => ⟨by convert bip_core_iff hCt ht ht3 hv hC hx hxW,
      by
        intro hb
        obtain ⟨s,hs⟩ := col_core_flip hCt ht ht3 hv hC hx hxW hb
        refine ⟨s,fun u hu => ?_⟩
        convert hs u (by simpa only [Finset.mem_inter] using hu) using 1 <;>
          congr 3 <;> congr 1 <;> apply Subsingleton.elim⟩,
    fun x hx hs => ⟨mem_MCore_of_contract hCt ht ht3 hx hs,
      (toCore_isLocalProfile hCt ht ht3 hx hs).1, (toCore_isLocalProfile hCt ht ht3 hx hs).2,
      l1E_toCore hs⟩⟩

end S07V48
