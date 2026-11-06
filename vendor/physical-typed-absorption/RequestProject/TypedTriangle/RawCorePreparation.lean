/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.RawProfileSampling
public import RequestProject.TypedTriangle.ChildNormalizedGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
namespace TypedTriangle.RawReference
open S07V24 S07V48

/-- One RAW host produces one and the SAME sampled core for the profile,
geometry, physical-profile contract and all later positive withdrawals.
H2 and an exact H1 seed of the raw host are NOT assumptions. Later demands
still have to belong to the original physical lattice. This is a single-layer
constructor, not a uniform multiscale vortex. -/
theorem raw_core_positive_preparation (α q b δ τ : ℝ) (h : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1) (hb : 0 < b)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hτ : 0 < τ) (hh : 6 ≤ h) :
    ∃ (t : ℕ) (ε ξ : ℝ) (n₀ : ℕ), Odd t ∧ 3 ≤ t ∧ 0 < ε ∧ 0 < ξ ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (μ : Finset V → ℝ) (e : ℝ), e ≤ 1/2 →
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        (∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b/Fintype.card V) →
        (∀ E ∈ edges H, |bdry H F μ E-1| ≤ e) →
        ∃ W : Finset V, q*Fintype.card V/2 ≤ W.card ∧ (W.card:ℝ) < 2*q*Fintype.card V ∧
          S07V45.CorePathContract H.G H.lab F W t ∧
          S07V27.RouteProp H.G H.lab F t ε W ∧
          (∀ u v, H.G.Adj u v → |sampW H.G H.lab F μ W u v/q-1| ≤ e+2*δ) ∧
          CommonNbrCond (restrictedHost H (univ\W)) F ((1/2)*α/2^h) ∧
          HingeCond (restrictedHost H (univ\W)) F ((1/2)*α/2^h) h ∧
          ∀ (X B : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B.Adj]
            (r d : ℕ), X ≤ H.G → (∀ v, X.degree v ≤ r) → (∀ v, B.degree v ≤ d) →
            (r:ℝ) ≤ ξ*Fintype.card V → (d:ℝ) ≤ ξ*Fintype.card V →
            ∃ R : Finset (Sym2 V), Disjoint R (X.edgeFinset∪B.edgeFinset) ∧
              Basal H F R ∧ (∀ v, (SelSimul.edeg R v:ℝ) ≤ τ*Fintype.card V) ∧
              ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → IsPhysical H F L →
                ∃ P Y : Finset (Sym2 V), R∪L = P∪Y ∧ Disjoint P Y ∧ Basal H F P ∧
                  (∀ E ∈ Y, ∀ v ∈ E, v ∈ W) ∧
                  (∀ v, (SelSimul.edeg Y v:ℝ) ≤ τ*Fintype.card V) ∧ IsPhysical H F Y := by
  have hθ : 0 < δ^2*q^2/(8*b) := by positivity
  obtain ⟨t,a,ε,nS,ht,ht3,ha,hε,hSample⟩ :=
    S07_core_ext α q (δ^2*q^2/(8*b)) h hα hq hq1 hh hθ
  obtain ⟨ξ,nD,hξ,hWithdraw⟩ := CorePaid.fixed_core_positive_withdrawal_covered
    α q τ ε t hα hq hτ ht ht3 hε
  refine ⟨t,ε,ξ,max (max nS nD) 1,ht,ht3,hε,hξ,?_⟩
  intro V I _ H F μ e he hn h3 h4 hμ hload
  have hnS : nS ≤ Fintype.card V := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnD : nD ≤ Fintype.card V := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn0 : 0 < Fintype.card V := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn)
  have hcount : Fintype.card (V×V×Bool) ≤ 2*Fintype.card V^2 := by
    simp only [Fintype.card_prod,Fintype.card_bool]; nlinarith
  obtain ⟨W,hWlo,hWhi,hpool,hhinge,hroute,hbad⟩ := hSample V I H.G H.lab F h3 h4 hnS
    (V×V×Bool) hcount (rawProfileBad H F μ q δ)
      (raw_profile_bad_prob hb he hq hq1 hδ hδ1 hn0 hμ hload)
  have hCt : S07V45.CorePathContract H.G H.lab F W t := by
    apply S07V45.contract_of_route (by omega)
    intro v x y hxy
    obtain ⟨p,hp,hW,-,-⟩ := hroute ∅ ⊥ 0 (by simp; positivity)
      (fun u => by simp) (by simp; positivity) v x y hxy
    exact ⟨p,hp,hW⟩
  have hGeom := CorePaid.sampled_core_geometry_scaled H F hα hq
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ) ≤ 2) (by omega) h4 W hWhi.le
      (fun u v huv k hk => by
        have hp := hpool u v huv k hk
        change q*α*(Fintype.card V:ℝ)/2 ≤ ((commonNbrs H k u v)∩W).card at hp
        nlinarith only [hp])
      (fun u v a b ht => by convert hhinge u v a b ht using 1 <;> ring)
  have hCov := CorePaid.edge_covered_of_approx μ (show e < 1 by linarith) hload
  refine ⟨W,hWlo,hWhi,hCt,hroute,?_,hGeom.1,hGeom.2,?_⟩
  · intro u v huv
    exact raw_profile_of_not_bad hb he hq hδ.le hμ hload hbad huv
  · exact hWithdraw H F W hCov hnD hWlo hpool hroute

end TypedTriangle.RawReference
