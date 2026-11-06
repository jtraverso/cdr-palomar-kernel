/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.FixedCorePaidSelector
public import RequestProject.TypedTriangle.G3SplitPayment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
namespace TypedTriangle.CorePaid
open SelSimul

/-- On the fixed core, avoid a geometrically sparse old stock while keeping
the new selector and mode degree arbitrarily thin. -/
theorem fixed_core_paid_selector_layer_split (α q0 τ ε : ℝ) (t : ℕ)
    (hα : 0 < α) (hq0 : 0 < q0) (hτ : 0 < τ)
    (ht : Odd t) (ht3 : 3 ≤ t) (hε : 0 < ε) :
    ∃ (θ δ : ℝ) (n₀ : ℕ), 0 < θ ∧ 0 < δ ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        IsPhysical H F (edges H) → n₀ ≤ Fintype.card V →
        q0*Fintype.card V/2 ≤ W.card →
        (∀ u v : V, u ≠ v → ∀ k : I, ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
          q0*α*Fintype.card V/2 ≤ ((commonNbrs H k u v) ∩ W).card) →
        S07V27.RouteProp H.G H.lab F t ε W →
          ∀ (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj]
            (r b : ℕ), X ≤ H.G →
            (∀ x y, X.Adj x y → x ∈ W ∨ y ∈ W) →
            (∀ v, X.degree v ≤ r) → (∀ v, B0.degree v ≤ b) →
            (r:ℝ) ≤ δ*Fintype.card V → (b:ℝ) ≤ θ*Fintype.card V →
            ∃ (σ : V → LocalSel V) (C : Finset (Sym2 V)),
              Disjoint (fuelU (univ \ W) σ ∪ C) (X.edgeFinset ∪ B0.edgeFinset) ∧
              Basal H F (fuelU (univ \ W) σ ∪ C) ∧
              Basal H F (residual X (univ \ W) σ ∅ ∪ C) ∧
              (∀ v, (edeg (fuelU (univ \ W) σ ∪ C) v:ℝ) ≤ τ*Fintype.card V) ∧
              ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → IsPhysical H F L →
                (fuelU (univ \ W) σ ∪ C) ∪ L =
                  packEdges (packing X (univ \ W) σ L) ∪ (residual X (univ \ W) σ L ∪ C) ∧
                Disjoint (packEdges (packing X (univ \ W) σ L)) (residual X (univ \ W) σ L ∪ C) ∧
                Basal H F (packEdges (packing X (univ \ W) σ L)) ∧
                (∀ e ∈ residual X (univ \ W) σ L ∪ C, ∀ v ∈ e, v ∈ W) ∧
                (∀ v, (edeg (residual X (univ \ W) σ L ∪ C) v:ℝ) ≤ τ*Fintype.card V) ∧
                IsPhysical H F (residual X (univ \ W) σ L ∪ C) := by
  let A := S07V27.selA t
  have hA : 0 < A := by dsimp [A,S07V27.selA]; omega
  obtain ⟨D,hD,hqBound⟩ := selQ_linear hε A
  let κ := q0*α/2
  let μ := q0/2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hμ : 0 < μ := by dsimp [μ]; positivity
  obtain ⟨θP,δP,nPay,hθP,hδP,hPay⟩ := payment_window_split κ μ τ hκ hμ hτ A D
  let θ := min (S07V27.selEps ε A) θP
  let δ := min (S07V27.selEps ε A) δP
  have hθ : 0 < θ := lt_min (S07V27.selEps_pos hε hA) hθP
  have hδ : 0 < δ := lt_min (S07V27.selEps_pos hε hA) hδP
  refine ⟨θ,δ,max nPay ⌈200/min ε 1⌉₊,hθ,hδ,?_⟩
  intro V I _ H F W h2 hn hWlow hpool' hroute
  intro X B0 _ _ r b hXG hXW hX hB hr hb
  have hlow : μ*Fintype.card V ≤ Fintype.card (Survivors (univ \ W)) := by
    rw [card_survivors_compl]
    dsimp [μ]
    nlinarith [hWlow]
  have hcore : CommonNbrCond (restrictedHost H (univ \ W)) F κ :=
    commonNbrCond_of_core_pool H F W hκ.le (by
      intro u v hne k hk
      have hp := hpool' u v hne k hk
      change κ*Fintype.card V ≤ _
      dsimp [κ]
      nlinarith [hp])
  have hrP : (r:ℝ) ≤ δP*Fintype.card V := hr.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  have hbP : (b:ℝ) ≤ θP*Fintype.card V := hb.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  obtain ⟨p,hp,hpWindow,hFuel,hRes⟩ := hPay (Fintype.card V)
    (Fintype.card (Survivors (univ \ W))) r b (S07V27.selQ ε A r)
    ((le_max_left _ _).trans hn) hlow (hqBound r) hrP hbP
  have hrS : (r:ℝ) ≤ S07V27.selEps ε A*Fintype.card V := hr.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hbS : (b:ℝ) ≤ S07V27.selEps ε A*Fintype.card V := hb.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have he : 0 < min ε 1 := lt_min hε one_pos
  have hn200 : 200 ≤ min ε 1*Fintype.card V := by
    have hc : (⌈200/min ε 1⌉₊:ℝ) ≤ Fintype.card V := by
      exact_mod_cast (le_max_right _ _).trans hn
    have hh := (Nat.le_ceil (200/min ε 1)).trans hc
    simpa only [mul_comm] using (div_le_iff₀ he).mp hh
  obtain ⟨hBud,hρ⟩ := S07V27.selector_window hε (t := t) (A := A)
    (by dsimp [A,S07V27.selA]; omega) hrS hbS hn200
  obtain ⟨hZW,hZ⟩ := S07V27.allRoots_hyps W X hXW
  obtain ⟨σ,C,hAvoid,hBas,hEmpty,hDeg,hModes⟩ := selector_paid_layer_host ht ht3 hε
    hroute X B0 (univ \ W) hZ hZW hXG h2 hcore
    (by dsimp [A,S07V27.selA]; omega) (S07V27.selQ_pos ε A r) hp hX hB hBud hρ hpWindow
  refine ⟨σ,C,hAvoid,hBas,hEmpty,?_,?_⟩
  · intro v
    exact (show (edeg (fuelU (univ \ W) σ ∪ C) v:ℝ) ≤
      ((max (A*r) (60*r+61*S07V27.selQ ε A r)+2*(61*r+60*S07V27.selQ ε A r+p):ℕ):ℝ) by
        exact_mod_cast hDeg v).trans hFuel
  · intro L hL hphys
    obtain ⟨heq,hd,hB,hW,hD,hPhys⟩ := hModes L hL hphys
    refine ⟨heq,hd,hB,?_,?_,hPhys⟩
    · intro e he v hv
      have := hW e he v hv
      simpa using this
    · intro v
      exact (show (edeg (residual X (univ \ W) σ L ∪ C) v:ℝ) ≤
        ((3*(61*r+60*S07V27.selQ ε A r)+2*p:ℕ):ℝ) by exact_mod_cast hD v).trans hRes


end TypedTriangle.CorePaid
