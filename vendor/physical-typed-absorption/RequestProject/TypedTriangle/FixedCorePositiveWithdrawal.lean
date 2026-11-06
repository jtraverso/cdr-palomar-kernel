/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.FixedCorePaidSelector
public import RequestProject.TypedTriangle.CorePositiveRefiner
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace TypedTriangle.CorePaid
open SelSimul S07V26

/-- Native positive withdrawal into the SPECIFIED sampled core. It does not
choose another core after the bank, seed profile or monitors have been fixed.
The root count is unrestricted and both modes have their original budgets.
Intrinsic child-lattice entry still requires the conserved-charge allocator. -/
theorem fixed_core_positive_withdrawal (α q0 τ ε : ℝ) (t : ℕ)
    (hα : 0 < α) (hq0 : 0 < q0) (hτ : 0 < τ)
    (ht : Odd t) (ht3 : 3 ≤ t) (hε : 0 < ε) :
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
            (r:ℝ) ≤ δ*Fintype.card V → (b:ℝ) ≤ δ*Fintype.card V →
            ∃ R : Finset (Sym2 V), Disjoint R (X.edgeFinset ∪ B.edgeFinset) ∧
              Basal H F R ∧ (∀ v, (edeg R v:ℝ) ≤ τ*Fintype.card V) ∧
              ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → IsPhysical H F L →
                ∃ P Y : Finset (Sym2 V),
                  R ∪ L = P ∪ Y ∧ Disjoint P Y ∧ Basal H F P ∧
                  (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
                  (∀ v, (edeg Y v:ℝ) ≤ τ*Fintype.card V) ∧ IsPhysical H F Y := by
  obtain ⟨δS,nS,hδS,hNative⟩ := fixed_core_paid_selector_layer α q0 (τ/2) ε t
    hα hq0 (by positivity) ht ht3 hε
  let κ := q0*α/2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨D,hD,hQ⟩ := forkQ_linear hκ
  let K : ℕ := D+6
  have hK : (1:ℝ) ≤ K := by dsimp [K]; exact_mod_cast (show 1 ≤ D+6 by omega)
  let u := min δS (τ/2)
  have hu : 0 < u := lt_min hδS (by positivity)
  let δ := min (forkEps κ) (u/(4*K))
  have hδ : 0 < δ := lt_min (forkEps_pos hκ) (by positivity)
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
  have hsize : b+3*r+forkQ κ r+4 ≤ b+K*(r+1) := by
    dsimp [K]
    nlinarith only [hQbound]
  have hδK : ((2:ℝ)*K+1)*δ ≤ u := by
    have hd := min_le_right (forkEps κ) (u/(4*K))
    change δ ≤ _ at hd
    have hx := (le_div_iff₀ (show (0:ℝ) < 4*K by positivity)).mp hd
    have hsmall : 2*K+1 ≤ (4:ℝ)*K := by linarith only [hK]
    exact (mul_le_mul_of_nonneg_right hsmall hδ.le).trans (by nlinarith only [hx])
  have hBounds : ((b+3*r+forkQ κ r+4:ℕ):ℝ) ≤ u*Fintype.card V := by
    have hs : ((b+3*r+forkQ κ r+4:ℕ):ℝ) ≤ b+K*(r+1) := by exact_mod_cast hsize
    have hc := mul_le_mul_of_nonneg_left
      (show (r:ℝ)+1 ≤ 2*δ*Fintype.card V by linarith only [hr,hδn])
      (show (0:ℝ) ≤ K by positivity)
    have hd := mul_le_mul_of_nonneg_right hδK hnR
    push_cast at hs ⊢
    nlinarith only [hs,hc,hd,hb]
  have hr1 : (r1:ℝ) ≤ δS*Fintype.card V := by
    have hhR : (r1:ℝ) ≤ ((b+3*r+forkQ κ r+4:ℕ):ℝ) := by
      exact_mod_cast (show r1 ≤ b+3*r+forkQ κ r+4 by dsimp [r1]; omega)
    exact (hhR.trans hBounds).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnR)
  have hb1 : (b1:ℝ) ≤ δS*Fintype.card V :=
    hBounds.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnR)
  have hRfSmall : ∀ v, (edeg Rf v:ℝ) ≤ (τ/2)*Fintype.card V := by
    intro v
    have h1 : (edeg Rf v:ℝ) ≤ ((b+3*r+forkQ κ r+4:ℕ):ℝ) := by
      have hh := hRfd v
      exact_mod_cast (show edeg Rf v ≤ b+3*r+forkQ κ r+4 by omega)
    exact (h1.trans hBounds).trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hnR)
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
  obtain ⟨σ,C,hAvoid,hBas,hEmpty,hDeg,hModes⟩ := hSel GX GB r1 b1
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
    hRfBas.union hBas hRfRp,?_,?_⟩
  · intro v
    have h1 := edeg_union_le Rf Rp v
    have h2 := hRfSmall v
    have h3 := hDeg v
    have h1R : (edeg (Rf ∪ Rp) v:ℝ) ≤ edeg Rf v+edeg Rp v := by exact_mod_cast h1
    linarith only [h1R,h2,h3]
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
    let Y := residual GX (univ \ W) σ L1 ∪ C
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
