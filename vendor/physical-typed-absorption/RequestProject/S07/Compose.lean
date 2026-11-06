/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07.ManyOddPaths
public import RequestProject.S07.HingeCore

@[expose] public section

/-!
# V24 / S07 §§1–2 composed: from component expansion + original H3/H4 to ONE robust core

* `card_pathsLen_induce_le` — a path in a component `(L v).induce C` is a path of the same
  length in the link `L v` (injectively).
* `window_ok` — the deletion window `|Z|, Δ(B) ≤ ε n` fits the deterministic count.
* `S07_layer12` — **the composed statement**. The constants `t` (odd), `a`, `ε`, `n₀` are fixed
  from `(c, κ, α, h, q)` BEFORE the host. For every host satisfying the ORIGINAL H3/H4 and
  every family of link components satisfying the S03 interfaces (minimum degree `c n`,
  maximum degree `≤ n`, ambient-normalised edge expansion `κ n` of the component, or of its
  double cover when the component is not declared bipartite), there is ONE `W` with
  `|W| ∈ [qn/2, 2qn)`, every H3 pool and every H4 hinge supply preserved at half its mean,
  and such that for EVERY later vertex set `Z` (`|Z| ≤ εn`) and EVERY graph `B` of maximum
  degree `≤ εn`, every admissible pair of every component still has a simple path of length
  exactly `t` in the original link, with all internal vertices in `W`, avoiding `Z`
  internally and using no edge of `B`.

The S03 interfaces (component degree/expansion, cover expansion) are hypotheses here: they are
intermediate consequences of H3/H4 (S03 §§4–6) that are NOT formalized in this run.
-/

open Finset

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace S07V24

open TypedTriangle.SparseEdge

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- paths in an induced subgraph are paths in the graph -/
theorem card_pathsLen_induce_le (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (t : ℕ) (x y : (C : Set V)) :
    (pathsLen (G.induce (C : Set V)) t x y).card ≤ (pathsLen G t x.1 y.1).card := by
  set f := (SimpleGraph.Embedding.induce (G := G) (C : Set V)).toHom
  have hf : Function.Injective f := (SimpleGraph.Embedding.induce (G := G) _).injective
  refine Finset.card_le_card_of_injOn (fun p => p.map f) ?_ ?_
  · intro p hp
    simp only [pathsLen, coe_filter, Set.mem_setOf_eq, SimpleGraph.mem_finsetWalkLength_iff] at hp ⊢
    exact ⟨by rw [SimpleGraph.Walk.length_map]; exact hp.1,
      SimpleGraph.Walk.map_isPath_of_injective hf hp.2⟩
  · intro p _ q _ h
    exact SimpleGraph.Walk.map_injective_of_injective hf _ _ h

omit [Fintype V] [DecidableEq V] in
/-- the deletion window fits the deterministic count -/
lemma window_ok {a q : ℝ} {m n : ℕ} (ha : 0 < a) (hq : 0 < q) (hm : 0 < m) (hn : 0 < n)
    (Z : Finset V) (d : ℕ) (hZ : (Z.card : ℝ) ≤ epsOf a q m * n) (hd : (d : ℝ) ≤ epsOf a q m * n) :
    ((Z.card * m + (m + 1) * d : ℕ) : ℝ) * (n : ℝ) ^ (m - 1) < a * q ^ m * (n : ℝ) ^ m / 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set ε := epsOf a q m
  have hε : ε * (2 * m + 1) = a * q ^ m / 4 := by
    simp only [ε, epsOf]; field_simp
  have hpow : (n : ℝ) ^ m = (n : ℝ) ^ (m - 1) * n := by rw [← pow_succ, Nat.sub_add_cancel hm]
  have hnm : 0 < (n : ℝ) ^ (m - 1) := by positivity
  have key : ((Z.card * m + (m + 1) * d : ℕ) : ℝ) ≤ ε * (2 * m + 1) * n := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hZ hmR.le, mul_le_mul_of_nonneg_left hd
      (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  rw [hε] at key
  have hq' : 0 < a * q ^ m := by positivity
  calc ((Z.card * m + (m + 1) * d : ℕ) : ℝ) * (n : ℝ) ^ (m - 1)
      ≤ a * q ^ m / 4 * n * (n : ℝ) ^ (m - 1) := mul_le_mul_of_nonneg_right key hnm.le
    _ < a * q ^ m * (n : ℝ) ^ m / 2 := by rw [hpow]; nlinarith [mul_pos hq' (mul_pos hnm hnR)]

/-- the S03 interface for one component `C` of the link `L` (ambient order `n`) -/
def CompInterface (L : SimpleGraph V) [DecidableRel L.Adj] (c κ : ℝ) (n : ℕ) (C : Finset V)
    (bip : Prop) (col : V → Bool) : Prop :=
  (∀ w : (C : Set V), c * n ≤ (L.induce (C : Set V)).degree w) ∧
  (∀ w : (C : Set V), (L.induce (C : Set V)).degree w ≤ n) ∧
  (bip → (∀ w w' : (C : Set V), (L.induce (C : Set V)).Adj w w' → col w.1 ≠ col w'.1) ∧
    ∀ S : Finset (C : Set V), 2 * S.card ≤ Fintype.card (C : Set V) →
      κ * n * S.card ≤ cutCount (L.induce (C : Set V)) S) ∧
  (¬ bip → ∀ S : Finset (↥(C : Set V) × Bool),
    2 * S.card ≤ Fintype.card (↥(C : Set V) × Bool) →
      κ * n * S.card ≤ cutCount (dcover (L.induce (C : Set V))) S)

/-- admissible pairs of the declared components of `L v` -/
def AdmPair (comps : V → Finset (Finset V)) (bip : V → Finset V → Prop) (col : V → V → Bool)
    (v x y : V) : Prop :=
  ∃ C ∈ comps v, x ∈ C ∧ y ∈ C ∧ x ≠ y ∧ (bip v C → col v x ≠ col v y)

/-- the explicit path length / constant / threshold -/
noncomputable def mOf (c κ : ℝ) : ℕ := kOf c κ + 1
noncomputable def aOf (c κ : ℝ) : ℝ := (min c 1) ^ (kOf c κ + 3) / 4

/-- the interface of one component gives the link-level path count -/
theorem link_paths_of_interface (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ)
    (L : SimpleGraph V) [DecidableRel L.Adj] (n : ℕ) (hn : n0Of c κ ≤ n)
    (hV : Fintype.card V = n) (C : Finset V) (bip : Prop) (col : V → Bool)
    (hI : CompInterface L c κ n C bip col) (x y : V) (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y)
    (hcol : bip → col x ≠ col y) :
    aOf c κ * (n : ℝ) ^ mOf c κ ≤ (pathsLen L (mOf c κ + 1) x y).card := by
  obtain ⟨hmin, hmax, hbip, hnb⟩ := hI
  have hcard : Fintype.card (C : Set V) ≤ n := by
    rw [← hV]; exact Fintype.card_subtype_le _
  set x' : (C : Set V) := ⟨x, hx⟩
  set y' : (C : Set V) := ⟨y, hy⟩
  have htr := card_pathsLen_induce_le L C (kOf c κ + 2) x' y'
  have hcount : aOf c κ * (n : ℝ) ^ mOf c κ ≤
      (pathsLen (L.induce (C : Set V)) (kOf c κ + 2) x' y').card := by
    by_cases hb : bip
    · obtain ⟨hproper, hexp⟩ := hbip hb
      exact odd_paths_bip_explicit c κ hc hκ (L.induce (C : Set V)) n hn hmin hmax hcard hexp
        (fun w => col w.1) hproper x' y' (hcol hb)
    · exact odd_paths_nonbip_explicit c κ hc hκ (L.induce (C : Set V)) n hn hmin hmax hcard
        (hnb hb) x' y' (fun h => hxy (congrArg Subtype.val h))
  exact hcount.trans (by exact_mod_cast htr)

/-- **S07 §§1–2 composed.** -/
theorem S07_layer12 (c κ α q : ℝ) (h : ℕ) (hc : 0 < c) (hκ : 0 < κ) (hα : 0 < α)
    (hq : 0 < q) (hq1 : q ≤ 1) (hh : 6 ≤ h) :
    ∃ (t : ℕ) (a ε : ℝ) (n₀ : ℕ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)) (_ : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h),
        n₀ ≤ Fintype.card V →
        ∀ (L : V → SimpleGraph V) [∀ v, DecidableRel (L v).Adj]
          (comps : V → Finset (Finset V)) (bip : V → Finset V → Prop) (col : V → V → Bool),
          (∀ v, ∀ C ∈ comps v, CompInterface (L v) c κ (Fintype.card V) C (bip v C) (col v)) →
          ∃ W : Finset V,
            q * Fintype.card V / 2 ≤ W.card ∧ (W.card : ℝ) < 2 * q * Fintype.card V ∧
            (∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
              q * α * Fintype.card V / 2 ≤ ((commonNbrs G lab k u v) ∩ W).card) ∧
            (∀ u v a' b' : V, HingeTest G lab F u v a' b' →
              α * q ^ (hOrd hH4 u v a' b' - 4) *
                  (Fintype.card V : ℝ) ^ (hOrd hH4 u v a' b' - 4) / 2 ≤
                ((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
                  freeV u v a' b' J ⊆ W).card) ∧
            ∀ (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ),
              (Z.card : ℝ) ≤ ε * Fintype.card V → (∀ u, B.degree u ≤ d) →
              (d : ℝ) ≤ ε * Fintype.card V →
              ∀ v x y, AdmPair comps bip col v x y →
                ∃ p ∈ pathsLen (L v) t x y, intlSet (t - 1) p ⊆ W ∧
                  (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z) ∧
                  ∀ k < t, ¬ B.Adj (p.getVert k) (p.getVert (k + 1)) := by
  obtain ⟨hkodd, -⟩ := kOf_spec hc hκ
  set m := mOf c κ with hmdef
  set a := aOf c κ with hadef
  have hm : 0 < m := by simp [hmdef, mOf]
  have hapos : 0 < a := by
    have : 0 < min c 1 := lt_min hc one_pos
    simp only [hadef, aOf]; positivity
  refine ⟨m + 1, a, epsOf a q m, max (n0Of c κ) (n0H α q a h m),
    by simp only [hmdef, mOf]; exact hkodd.add_even even_two,
    by simp only [hmdef, mOf]; obtain ⟨j, hj⟩ := hkodd; omega, hapos,
    by simp only [epsOf]; positivity, ?_⟩
  intro V _ _ I G lab F hH3 hH4 hn L _ comps bip col hI
  set n := Fintype.card V with hndef
  have hn1 : n0Of c κ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : n0H α q a h m ≤ n := le_trans (le_max_right _ _) hn
  have hpaths : ∀ v x y, AdmPair comps bip col v x y →
      a * (n : ℝ) ^ m ≤ (pathsLen (L v) (m + 1) x y).card := by
    rintro v x y ⟨C, hC, hx, hy, hxy, hcol⟩
    exact link_paths_of_interface c κ hc hκ (L v) n hn1 rfl C (bip v C) (col v) (hI v C hC)
      x y hx hy hxy hcol
  obtain ⟨W, h1, h2, h3, h4, h5⟩ := random_core_H3H4 α q a h m hα hq hq1 hapos hh hm G lab F
    hH3 hH4 hn2 L (AdmPair comps bip col) hpaths
  refine ⟨W, h1, h2, h3, h4, ?_⟩
  intro Z B _ d hZ hB hd v x y hadm
  have hnpos : 0 < n := by
    have : 0 < n0H α q a h m := Nat.succ_pos _
    omega
  have hwin := window_ok hapos hq hm hnpos Z d hZ hd
  obtain ⟨p, hp, hW, hZ', hB'⟩ := pay_deterministic (L v) m x y W (h5 v x y hadm) Z B d hB
    (by rw [← hndef]; exact hwin)
  exact ⟨p, hp, by simpa using hW, by simpa using hZ', by simpa using hB'⟩

end S07V24
