/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V48.SeedPackage
public import RequestProject.TypedTriangle.VortexFixedSamplingRate
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace S07V48
open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V24 S07V25 S07V45

/-- **the SAME-CORE package with the raw fractional-seed profile and its persistence** -/
theorem S07_core_seed_package_uniform_rate (α q C : ℝ) (h : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 6 ≤ h) (hC : 0 < C) :
    ∃ (t : ℕ) (a ε σ : ℝ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧ 0 < σ ∧
      ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)) (_ : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h),
        n₀ ≤ Fintype.card V →
        ∀ φ : Finset V → ℝ, DiffuseSeed G lab F C φ →
          ∃ W : Finset V,
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
                  (commonNbrs ((G \ B).comap Subtype.val) (lab ∘ Subtype.val) k u v).card) := by
  obtain ⟨t, a, ε, ht, ht3, ha, hε, hmain⟩ :=
    S07_core_seed_uniform_rate α q C h hα hq hq1 hh hC
  set σ := sigmaOf α q ε h with hσdef
  have hσ := sigmaOf_pos hα hq hε h
  refine ⟨t, a, ε, σ, ht, ht3, ha, hε, hσ, ?_⟩
  intro δ hδ
  obtain ⟨n₀, hmainδ⟩ := hmain δ hδ
  refine ⟨max n₀ (⌈9 / (q * α)⌉₊ + 1), ?_⟩
  intro V _ _ I G lab F hH3 hH4 hn φ hφ
  set n := Fintype.card V with hndef
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn9 : (9 : ℝ) < q * α * n := by
    have h1 := Nat.le_ceil (9 / (q * α))
    have h2 : ((⌈9 / (q * α)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by
      exact_mod_cast le_trans (le_max_right _ _) hn
    push_cast at h2
    have h3 : 9 / (q * α) < n := by linarith
    rwa [div_lt_iff₀ (by positivity), mul_comm] at h3
  have hnR : (0 : ℝ) < n := by
    by_contra hc; push_neg at hc
    have : q * α * n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  obtain ⟨W, h1, h2, h3, h4, h5, h6⟩ := hmainδ V I G lab F hH3 hH4 hn0 φ hφ
  have hCt : CorePathContract G lab F W t := by
    apply contract_of_route (by omega)
    intro v x y hxy
    obtain ⟨p, hp, hW, -, -⟩ := h5 ∅ ⊥ 0 (by simp; positivity) (fun u => by simp)
      (by simp; positivity) v x y hxy
    exact ⟨p, hp, hW⟩
  refine ⟨W, h1, h2, h3, h4, h5, hCt, coreItems_of_contract hCt ht ht3, h6,
    fun u v huv => by rw [subSum_eq]; exact h6 u.1 v.1 huv,
    fun T hT => coeff_window hφ hC hq two_pos h1 h2 hT, ?_⟩
  intro Z hZ B _ d hB
  have hdel := core_delete_det hα hq hq1 hε ht hH4 hn9 h1 h2 h3 h4 h5 Z hZ
  obtain ⟨d1, d2, d3, -, d5, -⟩ := hdel
  have hCtZ : CorePathContract G lab F (W \ Z) t := by
    apply contract_of_route (by omega)
    intro v x y hxy
    obtain ⟨p, hp, hW, -, -⟩ := d5 ∅ ⊥ 0 (by simp; positivity) (fun u => by simp)
      (by simp; positivity) v x y hxy
    exact ⟨p, hp, hW⟩
  have hdR : ∀ u, (B.degree u : ℝ) ≤ d := fun u => by exact_mod_cast hB u
  have hpers : ∀ u v : V, G.Adj u v → ¬ B.Adj u v →
      |sampW (G \ B) lab F φ (W \ Z) u v / q - 1| ≤
        δ + ((exclC G (G \ B) lab F W (W \ Z) u v).card : ℝ) * C / (q * n) ∧
      (exclC G (G \ B) lab F W (W \ Z) u v).card ≤ Z.card + 2 * d ∧
      |sampW (G \ B) lab F φ (W \ Z) u v / q - 1| ≤
        δ + ((Z.card : ℝ) + 2 * d) * C / (q * n) := by
    intro u v huv hBuv
    have hp := profile_persist hφ hC hq (sdiff_le : G \ B ≤ G) (sdiff_subset : W \ Z ⊆ W)
      (h6 u v huv)
    have hc := card_exclC_le G lab F B W Z hBuv
    have hc' : (exclC G (G \ B) lab F W (W \ Z) u v).card ≤ Z.card + 2 * d := by
      have := hB u; have := hB v; omega
    refine ⟨hp, hc', hp.trans ?_⟩
    have hcR : ((exclC G (G \ B) lab F W (W \ Z) u v).card : ℝ) ≤ (Z.card : ℝ) + 2 * d := by
      exact_mod_cast hc'
    have : ((exclC G (G \ B) lab F W (W \ Z) u v).card : ℝ) * C / (q * n) ≤
        ((Z.card : ℝ) + 2 * d) * C / (q * n) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcR hC.le) (by positivity)
    linarith
  refine ⟨core_delete_det hα hq hq1 hε ht hH4 hn9 h1 h2 h3 h4 h5 Z hZ, hCtZ,
    coreItems_of_contract hCtZ ht ht3, hpers, ?_, fun T hT => coeff_window hφ hC hq
      (by norm_num) (by linarith) d2 hT, ?_⟩
  · intro u v huv
    rw [subSum_eq]
    have huv' := huv
    simp only [SimpleGraph.comap_adj, SimpleGraph.sdiff_adj] at huv'
    exact (hpers u.1 v.1 huv'.1 huv'.2).2.2
  · intro u v huv k hk
    have hp := d3 u.1 v.1 (fun h' => huv (Subtype.ext h')) k hk
    have hs := subtype_pool G B lab (W \ Z) k u v
    have := hdR u.1
    have := hdR v.1
    linarith


#print axioms S07_core_seed_package_uniform_rate

end S07V48
