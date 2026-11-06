/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexFixedWindowWithdrawal
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CorePaid
open CorePayment PreparedSupply SelSimul SelBridge SelTyped S07V26
variable {V I : Type*} [Fintype V]

/-- Every fuel edge meets the complement of the root set when bases and
auxiliary vertices avoid the roots. -/
theorem fuelU_meets_complement (Z : Finset V) (σ : V → LocalSel V)
    (hOutside : ∀ v ∈ Z, (∀ w ∈ (σ v).W, w ∉ Z) ∧
      ∀ e ∈ (σ v).P, ∀ y ∈ e, y ∉ Z) :
    ∀ e ∈ fuelU Z σ, ∃ v ∈ e, v ∉ Z := by
  intro e he
  obtain ⟨r,hr,he⟩ := mem_biUnion.mp he
  change e ∈ (σ r).P ∪ radial r (σ r).W at he
  rcases mem_union.mp he with he | he
  · induction e using Sym2.ind with
    | _ u v => exact ⟨u, by simp, (hOutside r hr).2 _ he u (by simp)⟩
  · obtain ⟨w,hw,rfl⟩ := mem_image.mp he
    exact ⟨w,by simp,(hOutside r hr).1 w hw⟩

theorem selector_paid_layer_host_with_core_incidence {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {t : ℕ} (ht : Odd t) (ht3 : 3 ≤ t)
    {ε α : ℝ} (hε : 0 < ε) {W : Finset V}
    (hroute : S07V27.RouteProp G lab F t ε W)
    (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj]
    (Z : Finset V) (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v')
    (hZW : Disjoint Z W) (hXG : X ≤ G)
    (hH2 : IsPhysical (⟨G,lab⟩ : Host V I) F (edges (⟨G,lab⟩ : Host V I)))
    (hCore : CommonNbrCond (restrictedHost (⟨G,lab⟩ : Host V I) Z) F α)
    {A q r b p : ℕ} (hA : 200*(t-1)+8 ≤ A) (hq : 0 < q) (hp : 0 < p)
    (hX : ∀ v, X.degree v ≤ r) (hB : ∀ v, B0.degree v ≤ b)
    (hBud : r+b+A*r*Fintype.card V/q+(A+1)*r+10*r+(t-1)*(200*r) ≤ ⌊ε*Fintype.card V⌋₊)
    (hρ : ((b+61*r+60*q+60:ℕ):ℝ) ≤ ε*Fintype.card V)
    (hPay : ((Fintype.card V*(61*r+60*q)/p +
      2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) <
        α*Fintype.card (Survivors Z)) :
    ∃ (σ : V → LocalSel V) (C : Finset (Sym2 V)),
      Disjoint (fuelU Z σ ∪ C) (X.edgeFinset ∪ B0.edgeFinset) ∧
      Basal (⟨G,lab⟩ : Host V I) F (fuelU Z σ ∪ C) ∧
      Basal (⟨G,lab⟩ : Host V I) F (SelSimul.residual X Z σ ∅ ∪ C) ∧
      (∀ e ∈ fuelU Z σ ∪ C, ∃ v ∈ e, v ∉ Z) ∧
      (∀ v, edeg (fuelU Z σ ∪ C) v ≤ max (A*r) (60*r+61*q)+2*(61*r+60*q+p)) ∧
      ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → IsPhysical (⟨G,lab⟩ : Host V I) F L →
        (fuelU Z σ ∪ C) ∪ L = packEdges (packing X Z σ L) ∪ (SelSimul.residual X Z σ L ∪ C) ∧
        Disjoint (packEdges (packing X Z σ L)) (SelSimul.residual X Z σ L ∪ C) ∧
        Basal (⟨G,lab⟩ : Host V I) F (packEdges (packing X Z σ L)) ∧
        (∀ f ∈ SelSimul.residual X Z σ L ∪ C, ∀ v ∈ f, v ∉ Z) ∧
        (∀ v, edeg (SelSimul.residual X Z σ L ∪ C) v ≤ 3*(61*r+60*q)+2*p) ∧
        IsPhysical (⟨G,lab⟩ : Host V I) F (SelSimul.residual X Z σ L ∪ C) := by
  have hcov : S07V26.EdgeCovered G lab F := S07V26.H2Phys.edgeCovered hH2
  have hlink : ∀ v ∈ Z, ∀ u, X.Adj v u → ∃ y, (ComponentRows.link G lab F v).Adj u y :=
    fun v _ u hu => S07V27.link_of_edgeCovered hcov hXG hu
  have hAvail : ∀ v ∈ Z, S07V27.CoreAvail G lab F v (X.neighborFinset v)
      (S07V27.rootAdm G lab F X v) A (r+b+A*r*Fintype.card V/q) (b+61*r+60*q) W := by
    intro v hv
    exact S07V27.coreAvail_root ht ht3 hε hroute X v (hlink v hv) hA (hX v) hBud hρ
  obtain ⟨σ,hFam,hAux⟩ := S07V27.schedule_core G lab F X B0 Z W hZW
    (S07V27.rootAdm G lab F X) hAvail hq hX hB le_rfl le_rfl
  have hAdm0 : ∀ v ∈ Z, S07V27.rootAdm G lab F X v ∅ :=
    fun v _ => S07V27.rootAdm_empty G lab F X v
  have hadm0 : ∀ v ∈ Z, S07V27.rootAdm G lab F X v (demand X ∅ v) := by
    simpa [SelSimul.demand] using hAdm0
  have hKd := (hFam.layer_partition hZ hX (empty_subset _) hadm0).2.2.2.2.2.2
  have hKcard := card_le_order_mul_degree (SelSimul.residual X Z σ ∅) hKd
  have hPay' : (((SelSimul.residual X Z σ ∅).card/p +
      2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) <
        α*Fintype.card (Survivors Z) := by
    have hn := Nat.add_le_add_right (Nat.div_le_div_right (c := p) hKcard)
      (2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p))
    have hR : (((SelSimul.residual X Z σ ∅).card/p +
        2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) ≤
        ((Fintype.card V*(61*r+60*q)/p +
        2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) := by exact_mod_cast hn
    exact hR.trans_lt hPay
  obtain ⟨C,hC,hAvoid,hBas,hEmp,hCZ,hCd,hModes⟩ := paid_core_family hFam hCore hp hZ hX hB hAdm0 hPay'
  have hIncidence : ∀ e ∈ fuelU Z σ ∪ C, ∃ v ∈ e, v ∉ Z := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact fuelU_meets_complement Z σ (hFam.outside_Z hZ) e he
    · induction e using Sym2.ind with
      | _ u v => exact ⟨u, by simp, hCZ _ he u (by simp)⟩
  refine ⟨σ,C,hAvoid,hBas,hEmp,hIncidence,?_,?_⟩
  · intro v
    exact (edeg_union_le _ _ v).trans
      (Nat.add_le_add (hFam.fuelU_edeg_le hZ hX v) (hCd v))
  · intro L hL hphys
    obtain ⟨heq,hd,hP,hYZ,hYd,hYP⟩ := hModes L hL
      (fun v _ => SelectorEntry.rootAdm_of_physical X hL hphys v)
    exact ⟨heq,hd,hP,hYZ,hYd,hYP hphys⟩

theorem fixed_core_paid_selector_layer_uniform_with_core_incidence (α q0 ε : ℝ) (t : ℕ)
    (hα : 0 < α) (hq0 : 0 < q0)
    (ht : Odd t) (ht3 : 3 ≤ t) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ τ : ℝ, 0 < τ →
    ∃ (δ : ℝ) (n₀ : ℕ), 0 < δ ∧
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
              Basal H F (SelSimul.residual X (univ \ W) σ ∅ ∪ C) ∧
              (∀ e ∈ fuelU (univ \ W) σ ∪ C, ∃ v ∈ e, v ∈ W) ∧
              (∀ v, (edeg (fuelU (univ \ W) σ ∪ C) v:ℝ) ≤ τ*Fintype.card V) ∧
              ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → IsPhysical H F L →
                (fuelU (univ \ W) σ ∪ C) ∪ L =
                  packEdges (packing X (univ \ W) σ L) ∪ (SelSimul.residual X (univ \ W) σ L ∪ C) ∧
                Disjoint (packEdges (packing X (univ \ W) σ L)) (SelSimul.residual X (univ \ W) σ L ∪ C) ∧
                Basal H F (packEdges (packing X (univ \ W) σ L)) ∧
                (∀ e ∈ SelSimul.residual X (univ \ W) σ L ∪ C, ∀ v ∈ e, v ∈ W) ∧
                (∀ v, (edeg (SelSimul.residual X (univ \ W) σ L ∪ C) v:ℝ) ≤ τ*Fintype.card V) ∧
                IsPhysical H F (SelSimul.residual X (univ \ W) σ L ∪ C) := by
  let A := S07V27.selA t
  have hA : 0 < A := by dsimp [A,S07V27.selA]; omega
  obtain ⟨D,hD,hqBound⟩ := selQ_linear hε A
  let κ := q0*α/2
  let μ := q0/2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hμ : 0 < μ := by dsimp [μ]; positivity
  obtain ⟨θP,hθP,hPayUniform⟩ := payment_window_uniform κ μ hκ hμ A D
  let θ := min (S07V27.selEps ε A) θP
  have hθ : 0 < θ := lt_min (S07V27.selEps_pos hε hA) hθP
  refine ⟨θ,hθ,?_⟩
  intro τ hτ
  obtain ⟨δP,nPay,hδP,hPay⟩ := hPayUniform τ hτ
  let δ := min (S07V27.selEps ε A) δP
  have hδ : 0 < δ := lt_min (S07V27.selEps_pos hε hA) hδP
  refine ⟨δ,max nPay ⌈200/min ε 1⌉₊,hδ,?_⟩
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
  obtain ⟨σ,C,hAvoid,hBas,hEmpty,hInc,hDeg,hModes⟩ := selector_paid_layer_host_with_core_incidence ht ht3 hε
    hroute X B0 (univ \ W) hZ hZW hXG h2 hcore
    (by dsimp [A,S07V27.selA]; omega) (S07V27.selQ_pos ε A r) hp hX hB hBud hρ hpWindow
  refine ⟨σ,C,hAvoid,hBas,hEmpty,?_,?_,?_⟩
  · intro e he
    obtain ⟨v,hv,hvZ⟩ := hInc e he
    exact ⟨v,hv,by simpa using hvZ⟩
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
      exact (show (edeg (SelSimul.residual X (univ \ W) σ L ∪ C) v:ℝ) ≤
        ((3*(61*r+60*S07V27.selQ ε A r)+2*p:ℕ):ℝ) by exact_mod_cast hD v).trans hRes



theorem fixed_core_positive_withdrawal_uniform_with_core_incidence (α q0 ε : ℝ) (t : ℕ)
    (hα : 0 < α) (hq0 : 0 < q0)
    (ht : Odd t) (ht3 : 3 ≤ t) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ τ : ℝ, 0 < τ →
    ∃ (δ : ℝ) (n₀ : ℕ), 0 < δ ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        IsPhysical H F (edges H) → n₀ ≤ Fintype.card V →
        q0*Fintype.card V/2 ≤ W.card →
        (∀ u v : V, u ≠ v → ∀ k : I, ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
          q0*α*Fintype.card V/2 ≤ ((commonNbrs H k u v) ∩ W).card) →
        S07V27.RouteProp H.G H.lab F t ε W →
          ∀ (X B : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B.Adj]
            (r b : ℕ), X ≤ H.G →
            (∀ v, X.degree v ≤ r) → (∀ v, B.degree v ≤ b) →
            (r:ℝ) ≤ δ*Fintype.card V → (b:ℝ) ≤ θ*Fintype.card V →
            ∃ R : Finset (Sym2 V), Disjoint R (X.edgeFinset ∪ B.edgeFinset) ∧
              Basal H F R ∧ (∀ e ∈ R, ∃ v ∈ e, v ∈ W) ∧ (∀ v, (edeg R v:ℝ) ≤ τ*Fintype.card V) ∧
              (∃ Y0 : Finset (Sym2 V), Basal H F Y0 ∧ Y0 ⊆ R ∧
                (∀ e ∈ Y0, ∀ v ∈ e, v ∈ W) ∧
                (∀ v, (edeg Y0 v:ℝ) ≤ τ*Fintype.card V)) ∧
              ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → IsPhysical H F L →
                ∃ P Y : Finset (Sym2 V),
                  R ∪ L = P ∪ Y ∧ Disjoint P Y ∧ Basal H F P ∧
                  (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
                  (∀ v, (edeg Y v:ℝ) ≤ τ*Fintype.card V) ∧ IsPhysical H F Y := by
  obtain ⟨θS,hθS,hSelector⟩ := fixed_core_paid_selector_layer_uniform_with_core_incidence α q0 ε t
    hα hq0 ht ht3 hε
  let κ := q0*α/2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨D,hD,hQ⟩ := forkQ_linear hκ
  let K : ℕ := D+6
  have hK : (1:ℝ) ≤ K := by dsimp [K]; exact_mod_cast (show 1 ≤ D+6 by omega)
  let θ := min (forkEps κ) (θS/4)
  have hθ : 0 < θ := lt_min (forkEps_pos hκ) (by positivity)
  refine ⟨θ,hθ,?_⟩
  intro τ hτ
  obtain ⟨δS,nS,hδS,hNative⟩ := hSelector (τ/2) (by positivity)
  let u := min δS (τ/2)
  have hu : 0 < u := lt_min hδS (by positivity)
  let δ := min (forkEps κ) (min (u/(4*K)) (θS/(8*K)))
  have hδ : 0 < δ := lt_min (forkEps_pos hκ) (lt_min (by positivity) (by positivity))
  refine ⟨δ,max (max nS ⌈32/κ⌉₊) ⌈1/δ⌉₊,hδ,?_⟩
  intro V I _ H F W h2 hn hWlow hpool hroute
  have hSel := hNative H F W h2
    ((le_max_left _ _).trans ((le_max_left _ _).trans hn)) hWlow hpool hroute
  intro X B _ _ r b hXG hX hB hr hb
  have hnR : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hδn : 1 ≤ δ*Fintype.card V := by
    have hcn : (⌈1/δ⌉₊:ℝ) ≤ Fintype.card V := by exact_mod_cast (le_max_right _ _).trans hn
    have hv := (Nat.le_ceil (1/δ)).trans hcn
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hv
  have hn32 : 32 ≤ κ*Fintype.card V := by
    have hcn : (⌈32/κ⌉₊:ℝ) ≤ Fintype.card V := by
      exact_mod_cast (le_max_right _ _).trans ((le_max_left _ _).trans hn)
    have hv := (Nat.le_ceil (32/κ)).trans hcn
    simpa only [mul_comm] using (div_le_iff₀ hκ).mp hv
  have hrF : (r:ℝ) ≤ forkEps κ*Fintype.card V :=
    hr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnR)
  have hbF : (b:ℝ) ≤ forkEps κ*Fintype.card V :=
    hb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnR)
  have hXE : X.edgeFinset ⊆ edges H := by
    intro e he
    exact mem_filter.mpr ⟨mem_univ _,SimpleGraph.edgeSet_mono hXG (by simpa using he)⟩
  have hXd : ∀ v, SparseEdge.degIn X.edgeFinset v ≤ r := by
    intro v
    change edeg X.edgeFinset v ≤ r
    rw [edeg_edgeFinset]
    exact hX v
  have hBd : ∀ v, SparseEdge.degIn B.edgeFinset v ≤ b := by
    intro v
    change edeg B.edgeFinset v ≤ b
    rw [edeg_edgeFinset]
    exact hB v
  obtain ⟨fk,hFS,hRfDeg⟩ := forks_on_core_pool W hκ (by
      intro v w hne k hk
      have hv := hpool v w hne k hk
      calc κ*Fintype.card V = q0*α*Fintype.card V/2 := by dsimp [κ]; ring
           _ ≤ _ := hv) h2 X.edgeFinset B.edgeFinset hXE hXd hBd hrF hbF hn32
  let Rf := forkUnion (XZ X.edgeFinset W) fk
  let X1 := (X.edgeFinset \ XZ X.edgeFinset W) ∪ QU fk (XZ X.edgeFinset W)
  let B1 := X.edgeFinset ∪ B.edgeFinset ∪ Rf
  let r1 := 3*r+forkQ κ r+4
  let b1 := b+3*r+forkQ κ r+4
  have hRfBas : Basal H F Rf := fork_union_basal hFS
  have hRfE : Rf ⊆ edges H := basal_subset_edges hRfBas
  have hRfAvoid : Disjoint Rf (X.edgeFinset ∪ B.edgeFinset) := by
    apply disjoint_left.mpr
    intro e he he'
    obtain ⟨f,hf,he⟩ := mem_biUnion.mp he
    exact disjoint_left.mp (hFS.2.2 f hf) he he'
  have hRfInc : ∀ e ∈ Rf, ∃ v ∈ e, v ∈ W := by
    intro e he
    obtain ⟨f,hf,he⟩ := mem_biUnion.mp he
    have hValid := (hFS.1 f hf).2
    change e ∈ (fk f).B ∪ (fk f).Q at he
    rcases mem_union.mp he with he | he
    · exact hValid.B_meets_W e he
    · exact hValid.Q_meets_W e he
  have hRfd : ∀ v, edeg Rf v ≤ 2*r+forkQ κ r+4 := hRfDeg
  obtain ⟨_,_,_,_,_,hX1W,hX1Deg⟩ := hFS.fork_L (L := ∅) (empty_subset _)
  change ∀ e ∈ X1, ∃ v ∈ e, v ∈ W at hX1W
  change ∀ v, SparseEdge.degIn X1 v ≤ SparseEdge.degIn X.edgeFinset v+SparseEdge.degIn Rf v at hX1Deg
  have hX1d : ∀ v, edeg X1 v ≤ r1 := by
    intro v
    have h1 := hX1Deg v
    have h2 : edeg X.edgeFinset v ≤ r := by rw [edeg_edgeFinset]; exact hX v
    have h3 := hRfd v
    change edeg X1 v ≤ edeg X.edgeFinset v+edeg Rf v at h1
    dsimp [r1]
    omega
  have hB1d : ∀ v, edeg B1 v ≤ b1 := by
    intro v
    have h1 := edeg_union_le (X.edgeFinset ∪ B.edgeFinset) Rf v
    have h2 := edeg_union_le X.edgeFinset B.edgeFinset v
    rw [edeg_edgeFinset,edeg_edgeFinset] at h2
    have h3 := hX v
    have h4 := hB v
    have h5 := hRfd v
    dsimp [B1,b1]
    omega
  have hQbound := hQ r
  have hsize : 3*r+forkQ κ r+4 ≤ K*(r+1) := by
    dsimp [K]
    nlinarith only [hQbound]
  have hδK : 2*(K:ℝ)*δ ≤ u := by
    have hd : δ ≤ u/(4*K) := (min_le_right _ _).trans (min_le_left _ _)
    have hx := (le_div_iff₀ (show (0:ℝ) < 4*K by positivity)).mp hd
    nlinarith [hK,hδ.le]
  have hδStock : 2*(K:ℝ)*δ ≤ θS/4 := by
    have hd : δ ≤ θS/(8*K) := (min_le_right _ _).trans (min_le_right _ _)
    have hx := (le_div_iff₀ (show (0:ℝ) < 8*K by positivity)).mp hd
    nlinarith
  have hNewBounds : ((3*r+forkQ κ r+4:ℕ):ℝ) ≤ u*Fintype.card V := by
    have hs : ((3*r+forkQ κ r+4:ℕ):ℝ) ≤ K*(r+1) := by exact_mod_cast hsize
    have hc := mul_le_mul_of_nonneg_left
      (show (r:ℝ)+1 ≤ 2*δ*Fintype.card V by linarith only [hr,hδn])
      (show (0:ℝ) ≤ K by positivity)
    have hd := mul_le_mul_of_nonneg_right hδK hnR
    push_cast at hs ⊢
    nlinarith only [hs,hc,hd]
  have hStockBounds : ((b+3*r+forkQ κ r+4:ℕ):ℝ) ≤ θS*Fintype.card V := by
    have hs : ((3*r+forkQ κ r+4:ℕ):ℝ) ≤ K*(r+1) := by exact_mod_cast hsize
    have hc := mul_le_mul_of_nonneg_left
      (show (r:ℝ)+1 ≤ 2*δ*Fintype.card V by linarith only [hr,hδn])
      (show (0:ℝ) ≤ K by positivity)
    have hd := mul_le_mul_of_nonneg_right hδStock hnR
    have hθsmall : θ ≤ θS/4 := min_le_right _ _
    have hθn := mul_le_mul_of_nonneg_right hθsmall hnR
    push_cast at hs ⊢
    nlinarith only [hs,hc,hd,hθn,hb]
  have hr1 : (r1:ℝ) ≤ δS*Fintype.card V := by
    have hhR : (r1:ℝ) ≤ ((3*r+forkQ κ r+4:ℕ):ℝ) := by
      exact_mod_cast (show r1 ≤ 3*r+forkQ κ r+4 by dsimp [r1]; omega)
    exact (hhR.trans hNewBounds).trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hnR)
  have hb1 : (b1:ℝ) ≤ θS*Fintype.card V := by
    simpa only [b1] using hStockBounds
  have hRfSmall : ∀ v, (edeg Rf v:ℝ) ≤ (τ/2)*Fintype.card V := by
    intro v
    have h1 : (edeg Rf v:ℝ) ≤ ((3*r+forkQ κ r+4:ℕ):ℝ) := by
      have hh := hRfd v
      exact_mod_cast (show edeg Rf v ≤ 3*r+forkQ κ r+4 by omega)
    exact (h1.trans hNewBounds).trans
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hnR)
  have hX1E : X1 ⊆ edges H := by
    apply union_subset
    · exact sdiff_subset.trans hXE
    · exact ((hFS.fork_modes (I' := XZ X.edgeFinset W) subset_rfl).2.1).trans hRfE
  have hDiagX : ∀ e ∈ X1, ¬ e.IsDiag := edges_diagonal_free hX1E
  have hDiagB : ∀ e ∈ B1, ¬ e.IsDiag := by
    intro e he
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · exact X.not_isDiag_of_mem_edgeSet (by simpa using he)
      · exact B.not_isDiag_of_mem_edgeSet (by simpa using he)
    · exact edges_diagonal_free hRfE e he
  let GX := SimpleGraph.fromEdgeSet (X1:Set (Sym2 V))
  let GB := SimpleGraph.fromEdgeSet (B1:Set (Sym2 V))
  have hGX : GX.edgeFinset = X1 := edgeFinset_fromEdges X1 hDiagX
  have hGB : GB.edgeFinset = B1 := edgeFinset_fromEdges B1 hDiagB
  have hGXmem : ∀ e, e ∈ GX.edgeSet ↔ e ∈ X1 := fun e => by
    simpa only [SimpleGraph.mem_edgeFinset] using (Finset.ext_iff.mp hGX e)
  have hGBmem : ∀ e, e ∈ GB.edgeSet ↔ e ∈ B1 := fun e => by
    simpa only [SimpleGraph.mem_edgeFinset] using (Finset.ext_iff.mp hGB e)
  have hGXW : ∀ v w, GX.Adj v w → v ∈ W ∨ w ∈ W := by
    intro v w hvw
    obtain ⟨a,ha,hW⟩ := hX1W s(v,w) hvw.1
    rcases Sym2.mem_iff.mp ha with rfl | rfl
    · exact Or.inl hW
    · exact Or.inr hW
  obtain ⟨σ,C,hAvoid,hBas,hEmpty,hRpInc,hDeg,hModes⟩ := hSel GX GB r1 b1
    (fromEdges_le_host hX1E) hGXW (fromEdges_degree_le X1 hDiagX hX1d)
    (fromEdges_degree_le B1 hDiagB hB1d) hr1 hb1
  letI : Fintype GX.edgeSet := GX.fintypeEdgeSet
  letI : Fintype GB.edgeSet := GB.fintypeEdgeSet
  let Rp := fuelU (univ \ W) σ ∪ C
  have hAvoid' : Disjoint Rp (X1 ∪ B1) := by
    apply disjoint_left.mpr
    intro e he he'
    apply disjoint_left.mp hAvoid he
    rcases mem_union.mp he' with he' | he'
    · exact mem_union_left _ (SimpleGraph.mem_edgeFinset.mpr ((hGXmem e).mpr he'))
    · exact mem_union_right _ (SimpleGraph.mem_edgeFinset.mpr ((hGBmem e).mpr he'))
  have hRpOld : Disjoint Rp (X.edgeFinset ∪ B.edgeFinset ∪ Rf) :=
    hAvoid'.mono_right subset_union_right
  have hRfRp : Disjoint Rf Rp := (hRpOld.mono_right subset_union_right).symm
  refine ⟨Rf ∪ Rp,disjoint_union_left.mpr ⟨hRfAvoid,hRpOld.mono_right subset_union_left⟩,
    hRfBas.union hBas hRfRp,?_,?_,?_,?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · exact hRfInc e he
    · exact hRpInc e he
  · intro v
    have h1 := edeg_union_le Rf Rp v
    have h2 := hRfSmall v
    have h3 := hDeg v
    have h1R : (edeg (Rf ∪ Rp) v:ℝ) ≤ edeg Rf v+edeg Rp v := by exact_mod_cast h1
    linarith only [h1R,h2,h3]
  · let Y0 := SelSimul.residual GX (univ \ W) σ ∅ ∪ C
    obtain ⟨hEq0,_,_,hIn0,hDeg0,_⟩ :=
      hModes ∅ (empty_subset _) (isPhysical_empty H F)
    have hY0Rp : Y0 ⊆ Rp := by
      have hh : Rp = packEdges (packing GX (univ \ W) σ ∅) ∪ Y0 := by
        simpa only [union_empty] using hEq0
      rw [hh]
      exact subset_union_right
    refine ⟨Y0,hEmpty,hY0Rp.trans subset_union_right,hIn0,?_⟩
    intro v
    exact (hDeg0 v).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hτ]) hnR)
  · intro L hL hphys
    let I0 := L ∩ XZ X.edgeFinset W
    let L1 := (L \ I0) ∪ QU fk I0
    let Pf := (Rf \ QU fk I0) ∪ I0
    obtain ⟨hfEq,hfDisj,_,hDiff,hL1,_,_⟩ := hFS.fork_L hL
    change L ∪ Rf = L1 ∪ Pf at hfEq
    change Disjoint L1 Pf at hfDisj
    have hL1Phys : IsPhysical H F L1 := SelectorEntry.physical_of_difference hphys hDiff
    obtain ⟨hsEq,hsDisj,hPs,hYIn,hYDeg,hYP⟩ := hModes L1
      (fun e he => SimpleGraph.mem_edgeFinset.mpr ((hGXmem e).mpr (hL1 he))) hL1Phys
    let Ps := packEdges (packing GX (univ \ W) σ L1)
    let Y := SelSimul.residual GX (univ \ W) σ L1 ∪ C
    change Rp ∪ L1 = Ps ∪ Y at hsEq
    change Disjoint Ps Y at hsDisj
    have hPf : Basal H F Pf := fork_mode_basal hFS hL
    have hPfSub : Pf ⊆ L ∪ Rf := by rw [hfEq]; exact subset_union_right
    have hRpLR : Disjoint Rp (L ∪ Rf) := hRpOld.mono_right (union_subset
      (hL.trans (subset_union_left.trans subset_union_left)) subset_union_right)
    have hRpPf := hRpLR.mono_right hPfSub
    have hUnionPf : Disjoint (Rp ∪ L1) Pf := disjoint_union_left.mpr ⟨hRpPf,hfDisj⟩
    have hPsSub : Ps ⊆ Rp ∪ L1 := by rw [hsEq]; exact subset_union_left
    have hYSub : Y ⊆ Rp ∪ L1 := by rw [hsEq]; exact subset_union_right
    have hPsPf := hUnionPf.mono_left hPsSub
    have hYPf := hUnionPf.mono_left hYSub
    refine ⟨Ps ∪ Pf,Y,?_,disjoint_union_left.mpr ⟨hsDisj,hYPf.symm⟩,
      hPs.union hPf hPsPf,hYIn,?_,hYP⟩
    · calc (Rf ∪ Rp) ∪ L = (L ∪ Rf) ∪ Rp := by ac_rfl
           _ = (L1 ∪ Pf) ∪ Rp := by rw [hfEq]
           _ = (Rp ∪ L1) ∪ Pf := by ac_rfl
           _ = (Ps ∪ Y) ∪ Pf := by rw [hsEq]
           _ = (Ps ∪ Pf) ∪ Y := by ac_rfl
    · intro v
      exact (hYDeg v).trans (mul_le_mul_of_nonneg_right (by linarith only [hτ]) hnR)



end TypedTriangle.CorePaid
namespace TypedTriangle.Vortex
open CorePaid BasalIncidence SelSimul
theorem uniform_fixed_window_withdrawal_with_core_incidence {I : Type}
    (F : Set (Multiset I)) (α q ε : ℝ) (t : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hε : 0 < ε)
    (ht : Odd t) (ht3 : 3 ≤ t) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ τ : ℝ, 0 < τ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (W : Finset V),
      IsPhysical H F (edges H) → n₀ ≤ Fintype.card V →
      q * Fintype.card V / 2 ≤ W.card →
      (∀ u v : V, u ≠ v → ∀ k : I,
        ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
        q * α * Fintype.card V / 2 ≤ ((commonNbrs H k u v) ∩ W).card) →
      S07V27.RouteProp H.G H.lab F t ε W →
      ∀ (D : Finset (Finset V)) (T : Finset (Sym2 V)) (r b : ℕ),
        cover D ⊆ edges H → T ⊆ edges H →
        (∀ v, degIn (cover D) v ≤ r) →
        (∀ v, degIn T v ≤ b) →
        (r : ℝ) ≤ δ * Fintype.card V →
        (b : ℝ) ≤ θ * Fintype.card V →
        ∃ R : Finset (Sym2 V),
          Disjoint R (cover D ∪ T) ∧ Basal H F R ∧
          (∀ e ∈ R, ∃ v ∈ e, v ∈ W) ∧
          (∀ v, (edeg R v : ℝ) ≤ τ * Fintype.card V) ∧
          (∃ Y0 : Finset (Sym2 V), Basal H F Y0 ∧ Y0 ⊆ R ∧
            (∀ e ∈ Y0, ∀ v ∈ e, v ∈ W) ∧
            ∀ v, (edeg Y0 v : ℝ) ≤ τ * Fintype.card V) ∧
          ∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
            ∃ Ps Y : Finset (Sym2 V),
              R ∪ L = Ps ∪ Y ∧ Disjoint Ps Y ∧ Basal H F Ps ∧
              (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
              (∀ v, (edeg Y v : ℝ) ≤ τ * Fintype.card V) ∧
              IsPhysical H F Y := by
  obtain ⟨θ,hθ,hWithdraw⟩ := fixed_core_positive_withdrawal_uniform_with_core_incidence α q ε t
    hα hq ht ht3 hε
  refine ⟨θ,hθ,?_⟩
  intro τ hτ
  obtain ⟨δ,n₀,hδ,hSel⟩ := hWithdraw τ hτ
  refine ⟨δ,hδ,n₀,?_⟩
  intro V _ H W h2 hn hW hpool hroute D T r b hD hT hdD hdT hr hb
  let X := SimpleGraph.fromEdgeSet (cover D : Set (Sym2 V))
  let B := SimpleGraph.fromEdgeSet (T : Set (Sym2 V))
  letI : DecidableRel X.Adj := Classical.decRel _
  letI : DecidableRel B.Adj := Classical.decRel _
  letI : Fintype X.edgeSet := X.fintypeEdgeSet
  letI : Fintype B.edgeSet := B.fintypeEdgeSet
  have hXmem (e : Sym2 V) : e ∈ X.edgeSet ↔ e ∈ cover D := by
    simp only [X, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe,
      Sym2.mem_diagSet]
    exact ⟨And.left, fun he => ⟨he, edges_diagonal_free hD e he⟩⟩
  have hBmem (e : Sym2 V) : e ∈ B.edgeSet ↔ e ∈ T := by
    simp only [B, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe,
      Sym2.mem_diagSet]
    exact ⟨And.left, fun he => ⟨he, edges_diagonal_free hT e he⟩⟩
  have hXd : ∀ v, X.degree v ≤ r := by
    intro v
    have hv := fromEdges_degree_le _ (edges_diagonal_free hD) hdD v
    convert hv using 1 <;> congr 2 <;> apply Subsingleton.elim
  have hBd : ∀ v, B.degree v ≤ b := by
    intro v
    have hv := fromEdges_degree_le _ (edges_diagonal_free hT) hdT v
    convert hv using 1 <;> congr 2 <;> apply Subsingleton.elim
  obtain ⟨R,hdis,hbasal,hInc,hdeg,hY0,hMode⟩ := hSel H F W h2 hn hW hpool hroute
    X B r b (fromEdges_le_host hD) hXd hBd hr hb
  refine ⟨R,?_,hbasal,hInc,hdeg,hY0,?_⟩
  · apply disjoint_left.mpr
    intro e heR he
    apply disjoint_left.mp hdis heR
    rcases mem_union.mp he with he | he
    · apply mem_union_left
      simpa only [SimpleGraph.mem_edgeFinset] using (hXmem e).mpr he
    · apply mem_union_right
      simpa only [SimpleGraph.mem_edgeFinset] using (hBmem e).mpr he
  · intro L hL hphys
    apply hMode L ?_ hphys
    intro e he
    simpa only [SimpleGraph.mem_edgeFinset] using (hXmem e).mpr (hL he)

/-- Incidence with a disjoint core excludes every edge internal to the
protected vertex set, regardless of the degree of that internal edge set. -/
theorem disjoint_of_core_incidence {V : Type*} [Fintype V]
    (W U : Finset V) (R E : Finset (Sym2 V))
    (hWU : Disjoint W U)
    (hR : ∀ e ∈ R, ∃ v ∈ e, v ∈ W)
    (hE : ∀ e ∈ E, ∀ v ∈ e, v ∈ U) : Disjoint R E := by
  apply disjoint_left.mpr
  intro e heR heE
  obtain ⟨v,hve,hvW⟩ := hR e heR
  exact disjoint_left.mp hWU hvW (hE e heE v hve)

#print axioms uniform_fixed_window_withdrawal_with_core_incidence
#print axioms disjoint_of_core_incidence
end TypedTriangle.Vortex
