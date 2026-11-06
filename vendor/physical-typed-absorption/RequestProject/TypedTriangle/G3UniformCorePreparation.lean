/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeSharedCorePreparation
public import RequestProject.TypedTriangle.G3UniformWithdrawal
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
namespace TypedTriangle.CorePaid
open SelSimul S07V26

/-- On the original H1--H4 host, choose the fixed protected-stock cap before
the demanded output degree; both contracts live on the same sampled core. -/
theorem native_shared_core_positive_preparation_uniform (α q0 C ξ : ℝ) (h : ℕ)
    (hα : 0 < α) (hq0 : 0 < q0) (hq1 : q0 ≤ 1)
    (hC : 1 ≤ C) (hξ : 0 < ξ) (hh : 6 ≤ h) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ τ : ℝ, 0 < τ →
    ∃ (t : ℕ) (ε δ : ℝ) (n₀ : ℕ), Odd t ∧ 3 ≤ t ∧ 0 < ε ∧ 0 < δ ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (φ : Finset V → ℝ),
        CommonNbrCond H F α → HingeCond H F α h → IsPhysical H F (edges H) →
        IsDiffuseSeed H F C φ → n₀ ≤ Fintype.card V →
        ∃ W : Finset V, q0*Fintype.card V/2 ≤ W.card ∧ (W.card:ℝ) < 2*q0*Fintype.card V ∧
          S07V45.CorePathContract H.G H.lab F W t ∧
          (∀ u v, H.G.Adj u v → |S07V48.sampW H.G H.lab F φ W u v/q0-1| ≤ ξ) ∧
          CommonNbrCond (restrictedHost H (univ\W)) F (α*q0^h/2) ∧
          HingeCond (restrictedHost H (univ\W)) F (α*q0^h/2) h ∧
          ∀ (X B : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B.Adj]
            (r b : ℕ), X ≤ H.G →
            (∀ v, X.degree v ≤ r) → (∀ v, B.degree v ≤ b) →
            (r:ℝ) ≤ δ*Fintype.card V → (b:ℝ) ≤ θ*Fintype.card V →
            ∃ R : Finset (Sym2 V), Disjoint R (X.edgeFinset ∪ B.edgeFinset) ∧
              Basal H F R ∧ (∀ v, (edeg R v:ℝ) ≤ τ*Fintype.card V) ∧
              (∃ Y0 : Finset (Sym2 V), Basal H F Y0 ∧ Y0 ⊆ R ∧
                (∀ e ∈ Y0, ∀ v ∈ e, v ∈ W) ∧
                (∀ v, (edeg Y0 v:ℝ) ≤ τ*Fintype.card V)) ∧
              ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → IsPhysical H F L →
                ∃ P Y : Finset (Sym2 V),
                  R ∪ L = P ∪ Y ∧ Disjoint P Y ∧ Basal H F P ∧
                  (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
                  (∀ v, (edeg Y v:ℝ) ≤ τ*Fintype.card V) ∧ IsPhysical H F Y := by
  have hCp : 0 < C := by linarith
  obtain ⟨t,a,ε,σ,nS,ht,ht3,ha,hε,hσ,hSample⟩ :=
    S07V48.S07_core_seed_package α q0 C ξ h hα hq0 hq1 hh hCp hξ
  obtain ⟨θ,hθ,hUniform⟩ := fixed_core_positive_withdrawal_uniform α q0 ε t hα hq0 ht ht3 hε
  refine ⟨θ,hθ,?_⟩
  intro τ hτ
  obtain ⟨δ,nD,hδ,hWithdraw⟩ := hUniform τ hτ
  refine ⟨t,ε,δ,max nS nD,ht,ht3,hε,hδ,?_⟩
  intro V I _ H F φ h3 h4 h2 hφ hn
  obtain ⟨W,hWlow,hWhi,hpool,hhinges,hroute,hCt,hItems,hRaw,hRest⟩ :=
    hSample V I H.G H.lab F h3 h4 ((le_max_left _ _).trans hn) φ (diffuse_seed_for_sample hφ)
  have hGeom := sampled_core_geometry H F hα hq0 hq1 hh h4 W hpool hhinges
  exact ⟨W,hWlow,hWhi,hCt,hRaw,hGeom.1,hGeom.2,
    hWithdraw H F W h2 ((le_max_right _ _).trans hn) hWlow hpool hroute⟩


end TypedTriangle.CorePaid
