/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexUniformPreparedSample
public import RequestProject.TypedTriangle.VortexFixedWindowResources
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000

namespace TypedTriangle.Vortex
open CorePaid BasalIncidence SelSimul

/-- A single sampled and prepared window supports the raw stock and the
physical positive selector. Every density, charge and degree budget is fixed
before the host; the stock, selector and eventual bank use the same trimmed
window. This theorem stops before constructing the bank. -/
theorem uniform_prepared_window_resources {I : Type} (F : Set (Multiset I))
    (α q C ξ η : ℝ) (h N : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hC : 1 ≤ C) (hξ : 0 < ξ) (hη : 0 < η) (hh : 6 ≤ h) :
    ∃ (t : ℕ) (ε τTrim β θT : ℝ), Odd t ∧ 3 ≤ t ∧
      0 < ε ∧ 0 < τTrim ∧ τTrim ≤ ε / 2 ∧ τTrim ≤ q / 8 ∧
      0 < q - 2 * τTrim ∧ τTrim * C / q ≤ ξ / 2 ∧
      0 < β ∧ 0 < θT ∧
      ∀ ρcap τcap : ℝ, 0 < ρcap → 0 < τcap →
        ∃ ρ κ τR : ℝ, 0 < ρ ∧ ρ ≤ ρcap ∧ 0 < κ ∧
          0 < τR ∧ τR ≤ τcap ∧ ρ ≤ τR ∧
          ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V]
            (H : Host V I) (φ : Finset V → ℝ),
            n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
            IsPhysical H F (edges H) → CommonNbrCond H F α →
            HingeCond H F α h →
            ∃ (W : Finset V) (A : Finset (Survivors (univ \ W))),
              let Aamb := liftVertexSet (univ \ W) A
              let W' := W \ Aamb
              (q - 2 * τTrim) * Fintype.card V / 2 ≤ W'.card ∧
              (W'.card : ℝ) < 2 * q * Fintype.card V ∧
              CommonNbrCond
                (restrictedHost (restrictedHost H (univ \ W)) A) F
                ((α * q ^ h / 2) / 2) ∧
              HingeCond
                (restrictedHost (restrictedHost H (univ \ W)) A) F
                ((α * q ^ h / 2) / 2) h ∧
              Dispersal.PreparedCore
                (restrictedHost (restrictedHost H (univ \ W)) A).G
                (restrictedHost (restrictedHost H (univ \ W)) A).lab
                F ((α * q ^ h / 2) / 4) h N β ∧
              S07V27.RouteProp H.G H.lab F t (ε / 2) W' ∧
              (∀ u v : V, u ≠ v → ∀ k : I,
                ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
                (q - 2 * τTrim) * (α / 2) * Fintype.card V / 2 ≤
                  ((commonNbrs H k u v) ∩ W').card) ∧
              Nonempty (TypedTriangle.SampleOut H F W'.card 0) ∧
              (∀ u v, H.G.Adj u v →
                |S07V48.sampW H.G H.lab F φ W' u v / q - 1| ≤
                  ξ + τTrim * C / q) ∧
              ∀ (T : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT : ℕ),
                IsDecomposition H F T DT →
                (∀ v, degIn T v ≤ dT) →
                (dT : ℝ) ≤ θT * Fintype.card V →
                ∃ (D : Finset (Finset V)) (R : Finset (Sym2 V)),
                  IsDecomposition H F (cover D) D ∧
                  Disjoint (cover D) T ∧
                  (∀ v, (degIn (cover D) v : ℝ) < ρ * Fintype.card V) ∧
                  (∀ u v, H.G.Adj u v →
                    κ * Fintype.card V ≤ (good H F D u v).card) ∧
                  Disjoint R (cover D ∪ T) ∧ Basal H F R ∧
                  (∀ v, (edeg R v : ℝ) ≤ τR * Fintype.card V) ∧
                  (∀ v, (degIn ((cover D ∪ R) ∪ T) v : ℝ) ≤ η * W'.card) ∧
                  (∃ Y0 : Finset (Sym2 V), Basal H F Y0 ∧ Y0 ⊆ R ∧
                    (∀ e ∈ Y0, ∀ v ∈ e, v ∈ W') ∧
                    ∀ v, (edeg Y0 v : ℝ) ≤ τR * Fintype.card V) ∧
                  ∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
                    ∃ Ps Y : Finset (Sym2 V),
                      R ∪ L = Ps ∪ Y ∧ Disjoint Ps Y ∧ Basal H F Ps ∧
                      (∀ e ∈ Y, ∀ v ∈ e, v ∈ W') ∧
                      (∀ v, (edeg Y v : ℝ) ≤ τR * Fintype.card V) ∧
                      IsPhysical H F Y := by
  obtain ⟨t,ε,τTrim,β,ht,ht3,hε,hτTrim,hτRoute,hτq,hqTrim,hτProfile,
    hβ,nPrep,hPrep⟩ :=
    uniform_prepared_sample_before_bank F α q C ξ h N hα hq hq1 hC hξ hh
  obtain ⟨θT,hθT,hResources⟩ :=
    uniform_fixed_window_resources F α (α/2) (q-2*τTrim) (ε/2) C η h t
      hα (by positivity) hqTrim (by positivity) hC hη ht ht3
  refine ⟨t,ε,τTrim,β,θT,ht,ht3,hε,hτTrim,hτRoute,hτq,hqTrim,
    hτProfile,hβ,hθT,?_⟩
  intro ρcap τcap hρcap hτcap
  obtain ⟨ρ,κ,τR,hρ,hρcap,hκ,hτR,hτcap,hρτ,nResources,hResources'⟩ :=
    hResources ρcap τcap hρcap hτcap
  refine ⟨ρ,κ,τR,hρ,hρcap,hκ,hτR,hτcap,hρτ,max nPrep nResources,?_⟩
  intro V _ H φ hn hSeed hPhys h3 h4
  have hnPrep : nPrep ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnResources : nResources ≤ Fintype.card V :=
    (le_max_right _ _).trans hn
  obtain ⟨W,A,hWlo,hWhi,hA,h3A,h4A,hPc,hRoute,hPool,hOut,hRaw⟩ :=
    hPrep H φ hnPrep hSeed hPhys h3 h4
  let Aamb := liftVertexSet (univ \ W) A
  let W' := W \ Aamb
  have hcard := Finset.card_sdiff_add_card_inter W Aamb
  have hinter : (W ∩ Aamb).card ≤ Aamb.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hW' : (q - 2*τTrim) * Fintype.card V / 2 ≤ W'.card := by
    have hc : ((W'.card : ℕ) : ℝ) + (W ∩ Aamb).card = W.card := by
      exact_mod_cast hcard
    have hi : ((W ∩ Aamb).card : ℝ) ≤ Aamb.card := by
      exact_mod_cast hinter
    dsimp [W']
    nlinarith [hWlo,hA]
  have hW'hi : (W'.card : ℝ) < 2 * q * Fintype.card V := by
    have hsub : W' ⊆ W := sdiff_subset
    have hc : (W'.card : ℝ) ≤ W.card := by exact_mod_cast card_le_card hsub
    exact lt_of_le_of_lt hc hWhi
  refine ⟨W,A,hW',hW'hi,h3A,h4A,hPc,hRoute,hPool,hOut,hRaw,?_⟩
  intro T DT dT hT hTd hTcap
  exact hResources' H φ W' T DT dT hnResources hSeed hPhys h3 h4
    hW' hPool hRoute hT hTd hTcap

#print axioms uniform_prepared_window_resources

end TypedTriangle.Vortex
