/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V45.CoreSubtype
@[expose] public section

/-!
# V45 §5 — specialization to the SAME core `W` of `S07V25.S07_core_H3H4`

* `contract_of_route` — the transparent `CorePathContract` is DERIVED from the route conclusion
  of `S07V25.S07_core_H3H4` (instance `Z = ∅`, `B = ⊥`, `d = 0`); it is not a new hypothesis.
* `S07_core_profile_H3H4` — from the ORIGINAL `CommonNbrCond` (H3) and `HingeCond` (H4) only, with
  the constants `t, a, ε, n₀` of V25 fixed before the host: ONE core `W`, chosen before every
  later edge vector, which carries
  - all quantitative guarantees of V25 verbatim (core size, common neighbours in `W`, hinges
    inside `W`, robust odd routes avoiding any small `Z` and sparse `B`);
  - the derived `CorePathContract`;
  - item 1: the active components of each core link are exactly the nonempty `C ∩ W`;
  - item 2: bipartiteness preserved/reflected, colourings equal up to one flip;
  - item 3: every core-supported vector of the ORIGINAL `localProfile` lies in `MCore`, and its
    restriction to the true core subtype is a local profile of `H.comap Subtype.val` with
    exact `ℓ¹` and zero-extension identities.
-/

open Finset

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace S07V45

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V24 S07V25

/-- **the contract is derived from V25's route conclusion** (instance `Z = ∅`, `B = ⊥`) -/
theorem contract_of_route {V I : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {lab : V → I} {F : Set (Multiset I)} {W : Finset V} {t : ℕ} (ht1 : 1 ≤ t)
    [∀ v, DecidableRel (link G lab F v).Adj]
    (hroute : ∀ v x y, AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C))
        (colG G lab F) v x y →
      ∃ p ∈ pathsLen (link G lab F v) t x y, intlSet (t - 1) p ⊆ W) :
    CorePathContract G lab F W t := by
  intro v _ x y hxy
  obtain ⟨p, hp, hW⟩ := hroute v x y (by convert hxy)
  unfold pathsLen at hp
  rw [Finset.mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hp
  refine ⟨p, hp.1, hp.2, fun i hi0 hit => hW ?_⟩
  rw [mem_intlSet]
  refine ⟨⟨i - 1, by omega⟩, ?_⟩
  simp only [intl]
  congr 1
  omega

open Classical in
/-- **ONE core from the ORIGINAL H3/H4, with intrinsic local-profile transfer** -/
theorem S07_core_profile_H3H4 (α q : ℝ) (h : ℕ) (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 6 ≤ h) :
    ∃ (t : ℕ) (a ε : ℝ) (n₀ : ℕ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)) (_ : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h),
        n₀ ≤ Fintype.card V →
          ∃ W : Finset V,
            -- V25 quantitative guarantees, verbatim
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
            -- the derived transparent contract
            CorePathContract G lab F W t ∧
            -- item 1
            (∀ v ∈ W, activeComps (indG G W) lab F v =
              ((activeComps G lab F v).filter (fun C => (C ∩ W).Nonempty)).image (· ∩ W)) ∧
            (∀ v ∈ W, ∀ C ∈ activeComps G lab F v, ∀ x ∈ C, x ∈ W →
              comp (indG G W) lab F v x = C ∩ W) ∧
            -- item 2
            (∀ v ∈ W, ∀ C ∈ activeComps G lab F v, ∀ x ∈ C, x ∈ W →
              (IsBip (indG G W) lab F (v, C ∩ W) ↔ IsBip G lab F (v, C)) ∧
              (IsBip G lab F (v, C) → ∃ s : Bool, ∀ u ∈ C ∩ W,
                col (indG G W) lab F (v, C ∩ W) u = xor s (col G lab F (v, C) u))) ∧
            -- item 3 (W is fixed before every edge vector)
            (∀ x : Sym2 V → ℤ, x ∈ localProfile G lab F → x ∈ CoreSupp G W →
              x ∈ MCore G lab F W ∧
              IsLocalProfile (G.comap (Subtype.val : {a // a ∈ W} → V)) (lab ∘ Subtype.val) F
                (toCore W x) ∧
              liftE (ι := (Subtype.val : {a // a ∈ W} → V)) (toCore W x) = x ∧
              l1E (toCore W x) = l1E x) := by
  obtain ⟨t, a, ε, n₀, ht, ht3, ha, hε, hmain⟩ := S07_core_H3H4 α q h hα hq hq1 hh
  refine ⟨t, a, ε, n₀, ht, ht3, ha, hε, ?_⟩
  intro V _ _ I G lab F hH3 hH4 hn
  obtain ⟨W, h1, h2, h3, h4, h5⟩ := hmain V I G lab F hH3 hH4 hn
  have hCt : CorePathContract G lab F W t := by
    apply contract_of_route (by omega)
    intro v x y hxy
    obtain ⟨p, hp, hW, -, -⟩ := h5 ∅ ⊥ 0 (by simp; positivity) (fun u => by simp)
      (by simp; positivity) v x y hxy
    exact ⟨p, hp, hW⟩
  refine ⟨W, h1, h2, h3, h4, h5, hCt, fun v hv => by convert activeComps_core hCt ht3 hv,
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

end S07V45
