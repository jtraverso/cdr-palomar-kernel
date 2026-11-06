/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexWithdrawalCoreIncidence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000

namespace TypedTriangle.Vortex
open CorePaid BasalIncidence SelSimul

/-- A diffuse raw host has completion stock and a positive physical selector
on any prescribed window carrying the relative pool and route tests. The
window is supplied after all degree budgets have been chosen. -/
theorem uniform_fixed_window_resources_protecting_vertices {I : Type}
    (F : Set (Multiset I)) (α C : ℝ) (h : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) :
    ∃ γS : ℝ, 0 < γS ∧
      ∀ (αW qW εW η : ℝ) (t : ℕ),
        0 < αW → 0 < qW → 0 < εW → 0 < η → Odd t → 3 ≤ t →
    ∃ θT : ℝ, 0 < θT ∧
      ∀ ρcap τcap : ℝ, 0 < ρcap → 0 < τcap →
      ∃ ρ κ τ : ℝ, 0 < ρ ∧ ρ ≤ ρcap ∧ 0 < κ ∧
        0 < τ ∧ τ ≤ τcap ∧ ρ ≤ τ ∧
        ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V]
          (H : Host V I) (φ : Finset V → ℝ) (W : Finset V)
          (U : Finset V) (T S : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT dS : ℕ),
          n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
          IsPhysical H F (edges H) →
          CommonNbrCond H F α → HingeCond H F α h →
          qW * Fintype.card V / 2 ≤ W.card →
          (∀ u v : V, u ≠ v → ∀ k : I,
            ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
            qW * αW * Fintype.card V / 2 ≤
              ((commonNbrs H k u v) ∩ W).card) →
          S07V27.RouteProp H.G H.lab F t εW W →
          IsDecomposition H F T DT → Disjoint T S →
          Disjoint W U → (∀ e ∈ S, ∀ v ∈ e, v ∈ U) →
          (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ γS*Fintype.card V →
          (∀ v, degIn T v ≤ dT) →
          (dT : ℝ) ≤ θT * Fintype.card V →
          ∃ (D : Finset (Finset V)) (R : Finset (Sym2 V)),
            IsDecomposition H F (cover D) D ∧
            Disjoint (cover D) (T ∪ S) ∧
            (∀ v, (degIn (cover D) v : ℝ) < ρ * Fintype.card V) ∧
            (∀ u v, H.G.Adj u v → κ * Fintype.card V ≤ (good H F D u v).card) ∧
            Disjoint R (cover D ∪ T) ∧ Basal H F R ∧
            (∀ e ∈ R, ∃ v ∈ e, v ∈ W) ∧ Disjoint R S ∧
            (∀ v, (edeg R v : ℝ) ≤ τ * Fintype.card V) ∧
            (∀ v, (degIn ((cover D ∪ R) ∪ T) v : ℝ) ≤ η * W.card) ∧
            (∃ Y0 : Finset (Sym2 V), Basal H F Y0 ∧ Y0 ⊆ R ∧
              (∀ e ∈ Y0, ∀ v ∈ e, v ∈ W) ∧
              ∀ v, (edeg Y0 v : ℝ) ≤ τ * Fintype.card V) ∧
            ∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
              ∃ Ps Y : Finset (Sym2 V),
                R ∪ L = Ps ∪ Y ∧ Disjoint Ps Y ∧ Basal H F Ps ∧
                (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
                (∀ v, (edeg Y v : ℝ) ≤ τ * Fintype.card V) ∧
                IsPhysical H F Y := by
  obtain ⟨θS,εR,γ,hθS,hεR,hγ,hStockWindow⟩ :=
    reserve_from_raw_profile F (1/C) C α h (by positivity)
      (by have hCp : 0 < C := by linarith
          exact (div_le_iff₀ hCp).mpr (by nlinarith)) hα
  refine ⟨γ,hγ,?_⟩
  intro αW qW εW η t hαW hqW hεW hη ht ht3
  obtain ⟨θP,hθP,hSelectorWindow⟩ :=
    uniform_fixed_window_withdrawal_with_core_incidence F αW qW εW t hαW hqW hεW ht ht3
  let θT := min θS (min θP (η*qW/16))
  have hθT : 0 < θT := lt_min hθS (lt_min hθP (by positivity))
  refine ⟨θT,hθT,?_⟩
  intro ρcap τcap hρcap hτcap
  let τ := min (η*qW/16) τcap
  have hτ : 0 < τ := lt_min (by positivity) hτcap
  obtain ⟨δ,hδ,nSel,hSel⟩ := hSelectorWindow τ hτ
  let ρ := min (δ/4) (min τ ρcap)
  have hρ : 0 < ρ := lt_min (by positivity) (lt_min hτ hρcap)
  obtain ⟨κ,hκ,nStock,hStock⟩ := hStockWindow ρ hρ
  let n₀ := max nStock (max nSel ⌈4/δ⌉₊)
  refine ⟨ρ,κ,τ,hρ,
    (min_le_right _ _).trans (min_le_right _ _),hκ,hτ,min_le_right _ _,
    (min_le_right _ _).trans (min_le_left _ _),n₀,?_⟩
  intro V _ H φ W U T S DT dT dS hn hSeed hPhys h3 h4 hW hpool hroute
    hT hTS hWU hSU hSd hScap hTd hTcap
  have hnStock : nStock ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnSel : nSel ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnδ : ⌈4/δ⌉₊ ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hδn : 4 ≤ δ*Fintype.card V := by
    have hh : (4/δ:ℝ) ≤ Fintype.card V :=
      (Nat.le_ceil _).trans (by exact_mod_cast hnδ)
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hh
  have hμ : ∀ U, IsAllowed H F U →
      (1/C)/Fintype.card V ≤ φ U ∧ φ U ≤ C/Fintype.card V := by
    intro U hU
    have hh := hSeed.1 U hU
    constructor
    · convert hh.1 using 1 <;> ring
    · exact hh.2
  have hTsub : T ⊆ edges H := basal_subset_edges ⟨DT,hT⟩
  have hθSbound : (dT:ℝ) ≤ θS*Fintype.card V :=
    hTcap.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  obtain ⟨D,hD,hDT,hDd,hSupply⟩ := hStock H φ T S DT dT dS hnStock h3 h4 hμ
    (by intro e he; have he' : e ∈ H.G.edgeSet := by simpa [edges] using he
        simpa [IsDiffuseSeed.bdry_eq_one hSeed he'] using hεR.le)
    hTsub hT hTS hTd hθSbound hSd hScap
  let r := ⌈ρ*Fintype.card V⌉₊
  have hr : (r:ℝ) ≤ δ*Fintype.card V := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ ρ*Fintype.card V by positivity)
    have hρδ : ρ ≤ δ/4 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hρδ
      (show (0:ℝ) ≤ Fintype.card V by positivity)]
  have hDdNat : ∀ v, degIn (cover D) v ≤ r := by
    intro v
    exact_mod_cast (hDd v).le.trans (Nat.le_ceil _)
  have hθPbound : (dT:ℝ) ≤ θP*Fintype.card V :=
    hTcap.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_left _ _)) (by positivity))
  obtain ⟨R,hRdis,hR,hRinc,hRd,hY0,hMode⟩ :=
    hSel H W hPhys hnSel hW hpool hroute D T r dT
      (basal_subset_edges ⟨D,hD⟩) hTsub hDdNat hTd hr hθPbound
  have hRS : Disjoint R S := disjoint_of_core_incidence W U R S hWU hRinc hSU
  have hF0 : ∀ v, (degIn ((cover D ∪ R) ∪ T) v : ℝ) ≤ η*W.card := by
    intro v
    have hu : (degIn ((cover D ∪ R) ∪ T) v : ℝ) ≤
        degIn (cover D) v + degIn R v + degIn T v := by
      have ha := edeg_union_le (cover D ∪ R) T v
      have hb := edeg_union_le (cover D) R v
      change degIn ((cover D ∪ R) ∪ T) v ≤ degIn (cover D ∪ R) v + degIn T v at ha
      change degIn (cover D ∪ R) v ≤ degIn (cover D) v + degIn R v at hb
      exact_mod_cast (show degIn ((cover D ∪ R) ∪ T) v ≤
        degIn (cover D) v + degIn R v + degIn T v by omega)
    have hx := (hDd v).le
    have hy := hRd v
    change (degIn R v : ℝ) ≤ τ * Fintype.card V at hy
    have hz : (degIn T v : ℝ) ≤ dT := by exact_mod_cast hTd v
    have hρτ : ρ ≤ τ := (min_le_right _ _).trans (min_le_left _ _)
    have hτbound : τ ≤ η*qW/16 := min_le_left _ _
    have hTbound : θT ≤ η*qW/16 :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hθTn := mul_le_mul_of_nonneg_right hTbound
      (show (0:ℝ) ≤ Fintype.card V by positivity)
    have hρτn := mul_le_mul_of_nonneg_right hρτ
      (show (0:ℝ) ≤ Fintype.card V by positivity)
    have hτn := mul_le_mul_of_nonneg_right hτbound
      (show (0:ℝ) ≤ Fintype.card V by positivity)
    have hWn := mul_le_mul_of_nonneg_left hW hη.le
    nlinarith [hu,hx,hy,hz,hTcap,hθTn,hρτn,hτn,hWn]
  exact ⟨D,R,hD,hDT,hDd,hSupply,
    hRdis,hR,hRinc,hRS,hRd,hF0,hY0,hMode⟩

#print axioms uniform_fixed_window_resources_protecting_vertices

end TypedTriangle.Vortex
