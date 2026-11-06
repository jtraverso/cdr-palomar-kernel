/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V49.SubtypeRoute
public import RequestProject.S07V49.HingeCountB
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# V49 §6 — the SAME-CORE package with the two edge-deletion gaps of LEDGER_V48 §7 closed

`S07_core_seed_edge_package α q C δ h` fixes `t, a, ε, σ, η, n₀` from `(α, q, h, C, δ)` BEFORE
the host and its seed (`η = etaOf α q ε h`, `n₀ ≥` the V48 threshold and `n1Of α q h`). For
every host with the ORIGINAL H3/H4, `n ≥ n₀`, and every original exact diffuse seed `φ`, there
is ONE `W` such that

* all conclusions of `S07V48.S07_core_seed_package` hold for `W` (verbatim; this includes the
  raw-seed persistence with the exact loss `δ + (|Z| + 2d) C/(qn)` for every later `Z`, `B`);
* for every later `Z` with `|Z| ≤ σ n` and every graph `B` with `Δ(B) ≤ d ≤ η n`, both chosen
  after `W`, the EDGE-DELETED surviving host `G \ B` on `W ∖ Z` satisfies:
  1. residual routes of length `t` in the link `L_v(G \ B)` (path edges AND spokes avoid `B`)
     for every RESIDUAL admissible pair, inside `W ∖ Z`, avoiding any `Z'` with
     `|Z'| + d ≤ (ε/2) n`;
  2. `CorePathContract (G \ B) lab F (W ∖ Z) t` and `CoreItems (G \ B) lab F (W ∖ Z)`;
  3. paths of length `t` in the link of the TRUE subtype host `(G \ B).comap val` on
     `{a // a ∈ W ∖ Z}`;
  4. the residual active components are exactly the intact parts `C.filter (¬ B v ·)` of the
     original ones, each a single residual component, bipartite iff `C` is;
  5. every H4 test of `G \ B` has, for some order `9 ≤ i ≤ 2h - 3`, at least
     `hingeConstB α q h · n^(i-4)` hinges of `G \ B` of order `i` with free vertices in `W ∖ Z`.

No exact seed, divisibility or physicality of any induced or surviving host is claimed.
The hinge bound is a ONE-STEP result for one deletion `(Z, B)` after `W`; it does not iterate
(a second application would start from order `≤ 2h - 3` and constant `hingeConstB`).
-/

open Finset

noncomputable section

namespace S07V49

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V24 S07V25 S07V45 S07V48

/-- the edge-deletion degree budget, fixed from `(α, q, ε, h)` before the host -/
def etaOf (α q ε : ℝ) (h : ℕ) : ℝ :=
  min (ε / 2) (min (q * α / 64) (α * q ^ h / (80 * 2 ^ (h.choose 2))))

/-- the extra size threshold, fixed from `(α, q, h)` before the host -/
def n1Of (α q : ℝ) (h : ℕ) : ℕ :=
  ⌈32 / (q * α)⌉₊ + ⌈16 * ((h : ℝ) + 1) * 2 ^ (h.choose 2) / (α * q ^ h)⌉₊ + 1

lemma etaOf_pos {α q ε : ℝ} (hα : 0 < α) (hq : 0 < q) (hε : 0 < ε) (h : ℕ) :
    0 < etaOf α q ε h := by
  unfold etaOf; apply lt_min (by positivity); apply lt_min <;> positivity

open Classical in
/-- **the SAME-CORE package with edge-deleted routes, contract, items and hinge statistics** -/
theorem S07_core_seed_edge_package (α q C δ : ℝ) (h : ℕ) (hα : 0 < α) (hq : 0 < q)
    (hq1 : q ≤ 1) (hh : 6 ≤ h) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ (t : ℕ) (a ε σ η : ℝ) (n₀ : ℕ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧ 0 < σ ∧ 0 < η ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)) (_ : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h),
        n₀ ≤ Fintype.card V →
        ∀ φ : Finset V → ℝ, DiffuseSeed G lab F C φ →
          ∃ W : Finset V,
            -- all V48 conclusions, verbatim, for this `W`
            (
              -- V25, verbatim
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
              -- V45
              CorePathContract G lab F W t ∧ CoreItems G lab F W ∧
              -- raw seed profile, every host edge (roots inside or outside `W`)
              (∀ u v : V, G.Adj u v → |sampW G lab F φ W u v / q - 1| ≤ δ) ∧
              -- raw seed profile on the true induced subtype, weights `φ(T)/q`
              (∀ u v : {a // a ∈ W}, (G.comap Subtype.val).Adj u v →
                |subSum G lab F φ W u v / q - 1| ≤ δ) ∧
              -- coefficient window in terms of `|W|`
              (∀ T, IsAllowed G lab F T →
                1 / (2 * C * W.card) ≤ φ T / q ∧ φ T / q ≤ 2 * C / W.card) ∧
              -- persistence after a later vertex deletion `Z` and sparse edge deletion `B`
              ∀ (Z : Finset V), (Z.card : ℝ) ≤ σ * Fintype.card V →
              ∀ (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ), (∀ u, B.degree u ≤ d) →
                -- V25 deletion conclusions for `W ∖ Z`
                (q * Fintype.card V / 4 ≤ (W \ Z).card ∧
                ((W \ Z).card : ℝ) < 2 * q * Fintype.card V ∧
                (∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
                  q * α * Fintype.card V / 4 ≤ ((commonNbrs G lab k u v) ∩ (W \ Z)).card) ∧
                (∀ u v a' b' : V, HingeTest G lab F u v a' b' →
                  α * q ^ (hOrd hH4 u v a' b' - 4) *
                      (Fintype.card V : ℝ) ^ (hOrd hH4 u v a' b' - 4) / 4 ≤
                    ((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
                      freeV u v a' b' J ⊆ W \ Z).card) ∧
                (∀ (Z' : Finset V) (B' : SimpleGraph V) [DecidableRel B'.Adj] (d' : ℕ),
                  (Z'.card : ℝ) ≤ ε / 2 * Fintype.card V → (∀ u, B'.degree u ≤ d') →
                  (d' : ℝ) ≤ ε * Fintype.card V →
                  ∀ v x y, AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C))
                      (colG G lab F) v x y →
                    ∃ p ∈ pathsLen (link G lab F v) t x y, intlSet (t - 1) p ⊆ W \ Z ∧
                      (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z') ∧
                      ∀ k < t, ¬ B'.Adj (p.getVert k) (p.getVert (k + 1))) ∧
                (∀ v, ∀ C ∈ activeComps G lab F v,
                  (∀ x ∈ C, q * α * Fintype.card V / 4 ≤
                    (univ.filter fun y => (link G lab F v).Adj x y ∧ y ∈ C ∩ (W \ Z)).card) ∧
                  (∀ x ∈ C ∩ (W \ Z), ∀ y ∈ C ∩ (W \ Z),
                    ∃ p : (link G lab F v).Walk x y, ∀ z ∈ p.support, z ∈ C ∩ (W \ Z)) ∧
                  (¬ IsBip G lab F (v, C) → ¬ IsBip G lab F (v, C ∩ (W \ Z))))) ∧
                -- V45 contract and items for `W ∖ Z`
                CorePathContract G lab F (W \ Z) t ∧ CoreItems G lab F (W \ Z) ∧
                -- raw profile persistence (ambient form), loss paid by excluded completions
                (∀ u v : V, G.Adj u v → ¬ B.Adj u v →
                  |sampW (G \ B) lab F φ (W \ Z) u v / q - 1| ≤
                    δ + ((exclC G (G \ B) lab F W (W \ Z) u v).card : ℝ) * C /
                      (q * Fintype.card V) ∧
                  (exclC G (G \ B) lab F W (W \ Z) u v).card ≤ Z.card + 2 * d ∧
                  |sampW (G \ B) lab F φ (W \ Z) u v / q - 1| ≤
                    δ + ((Z.card : ℝ) + 2 * d) * C / (q * Fintype.card V)) ∧
                -- raw profile persistence on the TRUE surviving subtype host
                (∀ u v : {a // a ∈ W \ Z}, ((G \ B).comap Subtype.val).Adj u v →
                  |subSum (G \ B) lab F φ (W \ Z) u v / q - 1| ≤
                    δ + ((Z.card : ℝ) + 2 * d) * C / (q * Fintype.card V)) ∧
                -- coefficient window in terms of `|W ∖ Z|`
                (∀ T, IsAllowed G lab F T →
                  1 / (4 * C * (W \ Z).card) ≤ φ T / q ∧ φ T / q ≤ 2 * C / (W \ Z).card) ∧
                -- inherited H3 pools on the TRUE surviving subtype host
                (∀ u v : {a // a ∈ W \ Z}, u ≠ v → ∀ k : I,
                  ({lab u.1, lab v.1, k} : Multiset I) ∈ F →
                  q * α * Fintype.card V / 4 - 2 * d ≤
                    (commonNbrs ((G \ B).comap Subtype.val) (lab ∘ Subtype.val) k u v).card)
            ) ∧
            -- the edge-deleted surviving host on the same `W`
            ∀ (Z : Finset V), (Z.card : ℝ) ≤ σ * Fintype.card V →
            ∀ (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ), (∀ u, B.degree u ≤ d) →
              (d : ℝ) ≤ η * Fintype.card V →
              -- (1) residual routes with all spokes intact
              (∀ Z' : Finset V, (Z'.card : ℝ) + d ≤ ε / 2 * Fintype.card V →
                ∀ v x y, OrigAdm (G \ B) lab F v x y →
                  ∃ p ∈ pathsLen (link (G \ B) lab F v) t x y, intlSet (t - 1) p ⊆ W \ Z ∧
                    ∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z') ∧
              -- (2) the actual V45 contract and items for the edge-deleted host
              CorePathContract (G \ B) lab F (W \ Z) t ∧ CoreItems (G \ B) lab F (W \ Z) ∧
              -- (3) routes on the TRUE surviving subtype host
              (∀ v x y : {a // a ∈ W \ Z}, OrigAdm (G \ B) lab F v.1 x.1 y.1 →
                ∃ p : (link ((G \ B).comap Subtype.val) (lab ∘ Subtype.val) F v).Walk x y,
                  p.length = t ∧ p.IsPath) ∧
              -- (4) original/residual components, survival of non-bipartite components
              (∀ v, activeComps (G \ B) lab F v =
                ((activeComps G lab F v).filter (fun C => ∃ z ∈ C, ¬ B.Adj v z)).image
                  (fun C => C.filter (fun z => ¬ B.Adj v z))) ∧
              (∀ v, ∀ C ∈ activeComps G lab F v, ∀ x ∈ C, ¬ B.Adj v x →
                comp (G \ B) lab F v x = C.filter (fun z => ¬ B.Adj v z) ∧
                (IsBip (G \ B) lab F (v, comp (G \ B) lab F v x) ↔ IsBip G lab F (v, C))) ∧
              -- (5) hinge statistics of the edge-deleted host, order `≤ 2h - 3`
              (∀ u v a' b' : V, HingeTest (G \ B) lab F u v a' b' →
                ∃ i, 9 ≤ i ∧ i ≤ 2 * h - 3 ∧
                  hingeConstB α q h * (Fintype.card V : ℝ) ^ (i - 4) ≤
                    ((hinges (G \ B) lab F u v a' b' i).filter fun J =>
                      freeV u v a' b' J ⊆ W \ Z).card) := by
  obtain ⟨t, a, ε, σ, n₀, ht, ht3, ha, hε, hσ, hmain⟩ :=
    S07_core_seed_package α q C δ h hα hq hq1 hh hC hδ
  set η := etaOf α q ε h with hηdef
  have hη := etaOf_pos hα hq hε h
  have hη1 : η ≤ ε / 2 := min_le_left _ _
  have hη2 : η ≤ q * α / 64 := (min_le_right _ _).trans (min_le_left _ _)
  have hη3 : η ≤ α * q ^ h / (80 * 2 ^ (h.choose 2)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨t, a, ε, σ, η, max n₀ (n1Of α q h), ht, ht3, ha, hε, hσ, hη, ?_⟩
  intro V _ instD I G lab F hH3 hH4 hn φ hφ
  obtain rfl : instD = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  set n := Fintype.card V with hndef
  -- size facts from `n1Of`
  have hn1 : n1Of α q h ≤ n := le_trans (le_max_right _ _) hn
  have hD : (0 : ℝ) < 2 ^ (h.choose 2) := by positivity
  have hqh : 0 < α * q ^ h := by positivity
  have hbig1 : 32 < q * α * n := by
    have h1 := Nat.le_ceil (32 / (q * α))
    have h2 : ((n1Of α q h : ℕ) : ℝ) ≤ n := by exact_mod_cast hn1
    unfold n1Of at h2; push_cast at h2
    have h3 : (0 : ℝ) ≤ ⌈16 * ((h : ℝ) + 1) * 2 ^ (h.choose 2) / (α * q ^ h)⌉₊ := by positivity
    have h4 : 32 / (q * α) < n := by linarith
    rw [div_lt_iff₀ (by positivity)] at h4; linarith
  have hbig2 : 16 * ((h : ℝ) + 1) * 2 ^ (h.choose 2) < α * q ^ h * n := by
    have h1 := Nat.le_ceil (16 * ((h : ℝ) + 1) * 2 ^ (h.choose 2) / (α * q ^ h))
    have h2 : ((n1Of α q h : ℕ) : ℝ) ≤ n := by exact_mod_cast hn1
    unfold n1Of at h2; push_cast at h2
    have h3 : (0 : ℝ) ≤ ⌈32 / (q * α)⌉₊ := by positivity
    have h4 : 16 * ((h : ℝ) + 1) * 2 ^ (h.choose 2) / (α * q ^ h) < n := by linarith
    rw [div_lt_iff₀ hqh] at h4; linarith
  obtain ⟨W, h1, h2, h3, h4, h5, hCt, hIt, h6, h7, h8, hpers⟩ :=
    hmain V I G lab F hH3 hH4 (le_trans (le_max_left _ _) hn) φ hφ
  refine ⟨W, ⟨h1, h2, h3, h4, h5, hCt, hIt, h6, h7, h8, hpers⟩, ?_⟩
  intro Z hZ B _ d hB hdη
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hdε2 : (d : ℝ) ≤ ε / 2 * n := hdη.trans (mul_le_mul_of_nonneg_right hη1 hnR)
  have hdε : (d : ℝ) ≤ ε * n := hdε2.trans (mul_le_mul_of_nonneg_right (by linarith) hnR)
  have hdqa : (d : ℝ) ≤ q * α / 64 * n := hdη.trans (mul_le_mul_of_nonneg_right hη2 hnR)
  have hdh : (d : ℝ) ≤ α * q ^ h / (80 * 2 ^ (h.choose 2)) * n :=
    hdη.trans (mul_le_mul_of_nonneg_right hη3 hnR)
  obtain ⟨⟨-, -, d3, d4, d5, d6⟩, -⟩ := hpers Z hZ B d hB
  have hR : RobustRoutes G lab F (W \ Z) t (ε / 2) ε := d5
  have hContr : CorePathContract (G \ B) lab F (W \ Z) t :=
    contract_sdiff (by omega) hR hB hdε hdε2
  -- residual routes for original admissible pairs with intact spokes, as walks
  have hRw : ∀ v x y, OrigAdm G lab F v x y → ¬ B.Adj v x → ¬ B.Adj v y →
      ∃ p : (link (G \ B) lab F v).Walk x y, p.length = t := by
    intro v x y hxy hx hy
    obtain ⟨p, hp, -, -⟩ := route_intact hR hB hdε ∅ (by simpa using hdε2) hxy hx hy
    simp only [pathsLen, mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hp
    exact ⟨p, hp.1⟩
  have hK : 2 * (d : ℝ) + 2 ≤ q * α * n / 4 := by nlinarith
  have hN : ∀ v, ∀ C ∈ activeComps G lab F v, ∀ x ∈ C, ¬ B.Adj v x → ∀ w,
      ∃ y, (link (G \ B) lab F v).Adj x y ∧ y ≠ w := by
    intro v C hC x hx hBx w
    obtain ⟨y, hy, -, hyw⟩ := resid_nbr (d6 v C hC).1 hB hK x hx hBx w
    exact ⟨y, hy, hyw⟩
  have hw1 : 2 + 4 * (d : ℝ) ≤ q * α * n / 8 := by nlinarith
  have hw2 : (5 * (d : ℝ) + h + 1) * 2 ^ (h.choose 2) ≤ α * q ^ h * n / 8 := by
    have e1 : (d : ℝ) * 2 ^ (h.choose 2) ≤ α * q ^ h / 80 * n := by
      have := mul_le_mul_of_nonneg_right hdh hD.le
      calc (d : ℝ) * 2 ^ (h.choose 2) ≤ α * q ^ h / (80 * 2 ^ (h.choose 2)) * n *
            2 ^ (h.choose 2) := this
        _ = α * q ^ h / 80 * n := by field_simp
    nlinarith
  refine ⟨fun Z' hZ' v x y hxy => residual_route hR hB hdε Z' hZ' hxy, hContr,
    coreItems_sdiff ht ht3 hR hB hdε hdε2, fun v x y hxy => subtype_route hContr v x y hxy,
    fun v => resid_activeComps ht (hRw v) (hN v),
    fun v C hC x hx hBx => (resid_survival ht hC (hRw v) (hN v C hC) hx hBx).2,
    fun u v a' b' hT => edge_hinge_count hα hq hq1 hh hH4 d4 d3 B d hB hw1 hw2 hT⟩

end S07V49
