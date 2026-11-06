module
public import RequestProject.TypedTriangle.PaschWeightedForkChoice
public import RequestProject.TypedTriangle.PaschRelativeTupleControl
public import RequestProject.TypedTriangle.PaschFloorMixedControl
public import RequestProject.TypedTriangle.PaschAmbientRootedMonitor
public import RequestProject.TypedTriangle.PaschProtectedPacking
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
noncomputable section

section PaschWeightedForkPool
open Finset Classical TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V26 S07V25
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I Ω : Type*} [Fintype V] [Fintype Ω]

/-- A single codegree shift for the literal fork system; the ambient/host
order ratio is kept visible for the frontend payment. -/
def forkPaschPayment (κ : ℝ) (L nAmbient nHost : ℕ) : ℝ :=
  3*(((nAmbient:ℝ)/nHost)*((L+4:ℕ):ℝ)^3/(κ/8))

theorem forkPaschPayment_nonneg {κ : ℝ} (hκ : 0 < κ) (L nAmbient nHost : ℕ) :
    0 ≤ forkPaschPayment κ L nAmbient nHost := by unfold forkPaschPayment; positivity

/-- The legacy fork induction retains its two actual modes and pays their
entire universe against the intact ambient family. -/
theorem weighted_fork_greedy_aux (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)}
    (W : Finset V) {κ : ℝ} (hκ : 0 < κ)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I, ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
      κ*Fintype.card V ≤ ((TypedTriangle.commonNbrs H k u v)∩W).card)
    (X P : Finset (Sym2 V)) (hXG : X ⊆ TypedTriangle.edges H) {r b : ℕ}
    (hcov : ∀ e ∈ XZ X W, ∃ T, SparseEdge.IsAllowed H.G H.lab F T ∧ e ∈ SparseEdge.triEdges T)
    (hX : ∀ x, TypedTriangle.SparseEdge.degIn X x ≤ r) (hP : ∀ x, TypedTriangle.SparseEdge.degIn P x ≤ b)
    (hr : (r:ℝ) ≤ forkEps κ*Fintype.card V) (hb : (b:ℝ) ≤ forkEps κ*Fintype.card V)
    (hn : 32 ≤ κ*Fintype.card V) (R0 : Finset (Finset Ω)) (L0 : ℕ)
    (hR0 : PairCodegreeBound R0 L0) :
    ∀ T ⊆ XZ X W, ∃ fk : Sym2 V → Fork V,
      (∀ e ∈ T, (fk e).root = e ∧ (fk e).Valid H.G H.lab F W) ∧
      (∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → Disjoint (fk e).E (fk e').E) ∧
      (∀ e ∈ T, Disjoint (fk e).E (X∪P)) ∧
      (∀ x, x ∉ W → TypedTriangle.SparseEdge.degIn (forkUnion T fk) x ≤ 2*TypedTriangle.SparseEdge.degIn T x) ∧
      (∀ x ∈ W, TypedTriangle.SparseEdge.degIn (forkUnion T fk) x ≤ forkQ κ r+3) ∧
      (∑ x ∈ W, TypedTriangle.SparseEdge.degIn (forkUnion T fk) x) ≤ 8*T.card ∧
      (count (R0∪mapConfiguration ι (forkModes T fk)):ℝ) ≤ count R0+
        (T.card:ℝ)*forkPaschPayment κ L0 (Fintype.card Ω) (Fintype.card V) := by
  let Q := forkQ κ r
  have hQ : 1 ≤ Q := one_le_forkQ κ r
  have hLoop : ∀ e ∈ XZ X W, ¬e.IsDiag := fun e he =>
    SparseEdge.not_isDiag_of_mem_edges (hXG (XZ_subset X W he))
  have hDegXZ : ∀ v, TypedTriangle.SparseEdge.degIn (XZ X W) v ≤ r :=
    fun v => (S07V26.degIn_mono (XZ_subset X W) v).trans (hX v)
  have hI : 2*((XZ X W).card:ℝ) ≤ Fintype.card V*r := by
    exact_mod_cast two_card_le hLoop hDegXZ
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨fun e => ⟨(Quot.out e).1, (Quot.out e).1, (Quot.out e).1, (Quot.out e).1,
      (Quot.out e).1⟩, by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · intro x _; simp [forkUnion, SparseEdge.degIn]
    · intro x _; simp [forkUnion, SparseEdge.degIn]
    · simp [forkUnion, SparseEdge.degIn]
    · simp [forkModes,modeDec,mapConfiguration]
  | insert e T heT ih =>
    intro hsub
    have heX : e ∈ XZ X W := hsub (mem_insert_self _ _)
    have hTX : T ⊆ XZ X W := (subset_insert _ _).trans hsub
    obtain ⟨fk, h1, h2, h3, h4, h5, h6, hCost⟩ := ih hTX
    set R := forkUnion T fk with hR
    set U := X ∪ P ∪ R with hUdef
    set S := W.filter (fun x => Q ≤ SparseEdge.degIn R x) with hS
    set D := b + 3 * r + Q + 3 with hD
    have hRd : ∀ x, SparseEdge.degIn R x ≤ 2 * r + Q + 3 := by
      intro x
      by_cases hx : x ∈ W
      · have := h5 x hx; omega
      · have := h4 x hx
        have := S07V26.degIn_mono (hTX.trans (XZ_subset X W)) x
        have := hX x; omega
    have hU : ∀ x, SparseEdge.degIn U x ≤ D := by
      intro x
      rw [hUdef]
      have := degIn_union_le (X ∪ P) R x
      have := degIn_union_le X P x
      have := hX x; have := hP x; have := hRd x; omega
    have hSsum : S.card * Q ≤ 8 * (XZ X W).card := by
      have e1 : S.card • Q ≤ ∑ x ∈ S, SparseEdge.degIn R x :=
        card_nsmul_le_sum _ _ _ (fun x hx => (mem_filter.1 hx).2)
      have e2 : ∑ x ∈ S, SparseEdge.degIn R x ≤ ∑ x ∈ W, SparseEdge.degIn R x :=
        sum_le_sum_of_subset (filter_subset _ _)
      have e3 := card_le_card hTX
      rw [smul_eq_mul] at e1
      omega
    have hwin' : (S.card:ℝ)+2*D+8 ≤ (7/8:ℝ)*κ*Fintype.card V := by
      have hh := fork_dense_window hκ (Nat.cast_nonneg _) hn hr hb hI hSsum
      simpa only [hD,Q] using hh
    have hPartial := fork_modes_partial_pairCodegree (H:=H) (F:=F) hTX h1 h2 h3
    have hPartialA := pairCodegreeBound_mapConfiguration ι (forkModes T fk) 2 hPartial
    let Rprev := R0∪mapConfiguration ι (forkModes T fk)
    have hPrev : PairCodegreeBound Rprev (L0+2) := hR0.union hPartialA
    obtain ⟨u, v, c, rfl, hadj⟩ := root_of_cover (hcov _ heX)
    have huW : u ∉ W := (mem_XZ.1 heX).2 u (by simp)
    have hvW : v ∉ W := (mem_XZ.1 heX).2 v (by simp)
    obtain ⟨f,hfu,hfv,hf,hfU,hwS,haS,hbS,hfCost⟩ :=
      weighted_fork_step ι H.G H.lab F W hκ (by
        intro u v huv k hk
        exact hpool u v huv k hk) hU hwin' huW hvW hadj Rprev (L0+2) hPrev
    have hfCost' : (count (Rprev∪mapConfiguration ι {f.T0,f.T1,f.T2}):ℝ) ≤
        count Rprev+forkPaschPayment κ L0 (Fintype.card Ω) (Fintype.card V) := by
      simpa only [forkPaschPayment,Ambient.orderRatio] using hfCost
    have hroot : f.root = s(u, v) := by rw [Fork.root, hfu, hfv]
    have hfR : Disjoint f.E R := hfU.mono_right subset_union_right
    have hfXP : Disjoint f.E (X ∪ P) := hfU.mono_right subset_union_left
    set fk' := Function.update fk s(u, v) f with hfk'
    have hfk'e : fk' s(u, v) = f := Function.update_self _ _ _
    have hfk'T : ∀ e' ∈ T, fk' e' = fk e' := fun e' he' =>
      Function.update_of_ne (fun h => heT (by rw [← h]; exact he')) _ _
    have hunion : forkUnion (insert s(u, v) T) fk' = f.E ∪ R := by
      rw [forkUnion, biUnion_insert, hfk'e, hR, forkUnion]
      congr 1
      exact biUnion_congr rfl fun e' he' => by rw [hfk'T e' he']
    have hsubR : ∀ e' ∈ T, (fk e').E ⊆ R := fun e' he' =>
      subset_biUnion_of_mem (fun e => (fk e).E) he'
    refine ⟨fk', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e' he'
      rcases mem_insert.1 he' with rfl | he'
      · rw [hfk'e]; exact ⟨hroot, hf⟩
      · rw [hfk'T e' he']; exact h1 e' he'
    · intro e' he' e'' he'' hne
      rcases mem_insert.1 he' with rfl | he' <;> rcases mem_insert.1 he'' with rfl | he''
      · exact absurd rfl hne
      · rw [hfk'e, hfk'T e'' he'']; exact hfR.mono_right (hsubR e'' he'')
      · rw [hfk'e, hfk'T e' he']; exact (hfR.mono_right (hsubR e' he')).symm
      · rw [hfk'T e' he', hfk'T e'' he'']; exact h2 e' he' e'' he'' hne
    · intro e' he'
      rcases mem_insert.1 he' with rfl | he'
      · rw [hfk'e]; exact hfXP
      · rw [hfk'T e' he']; exact h3 e' he'
    · intro x hx
      rw [hunion, degIn_insert_of_notMem heT]
      have := degIn_union_le f.E R x
      have := hf.degIn_root hx
      rw [hroot] at this
      have := h4 x hx
      omega
    · intro x hx
      rw [hunion]
      have hle := degIn_union_le f.E R x
      have hb := hf.degIn_aux hx
      obtain ⟨-, -, -, -, -, -, -, hwa, hwb, hab⟩ := hf.distinct
      have hsat : ∀ y, y ∉ S → y ∈ W → SparseEdge.degIn R y < Q := fun y hy hyW => by
        by_contra hc; exact hy (mem_filter.2 ⟨hyW, by omega⟩)
      by_cases hxw : x = f.w
      · rw [if_pos hxw, if_neg (by rw [hxw]; exact hwa), if_neg (by rw [hxw]; exact hwb)] at hb
        have := hsat x (hxw ▸ hwS) hx; omega
      by_cases hxa : x = f.a
      · rw [if_neg hxw, if_pos hxa, if_neg (by rw [hxa]; exact hab)] at hb
        have := hsat x (hxa ▸ haS) hx; omega
      by_cases hxb : x = f.b
      · rw [if_neg hxw, if_neg hxa, if_pos hxb] at hb
        have := hsat x (hxb ▸ hbS) hx; omega
      · rw [if_neg hxw, if_neg hxa, if_neg hxb] at hb
        have := h5 x hx; omega
    · rw [hunion, card_insert_of_notMem heT]
      calc ∑ x ∈ W, SparseEdge.degIn (f.E ∪ R) x ≤ ∑ x ∈ W, (SparseEdge.degIn f.E x + SparseEdge.degIn R x) :=
            sum_le_sum fun x _ => degIn_union_le _ _ x
        _ = ∑ x ∈ W, SparseEdge.degIn f.E x + ∑ x ∈ W, SparseEdge.degIn R x := sum_add_distrib
        _ ≤ 8 + 8 * T.card := Nat.add_le_add hf.sum_degIn_W h6
        _ = 8 * (T.card + 1) := by ring

    · have hMode : forkModes (insert s(u,v) T) fk' = {f.T0,f.T1,f.T2}∪forkModes T fk := by
        exact forkModes_insert_update T fk s(u,v) f heT
      have hSets : R0∪mapConfiguration ι (forkModes (insert s(u,v) T) fk') =
          Rprev∪mapConfiguration ι {f.T0,f.T1,f.T2} := by
        rw [hMode]
        simp only [mapConfiguration,map_union]
        ext U
        simp only [Rprev,mapConfiguration,mem_union]
        tauto
      rw [hSets,card_insert_of_notMem heT,Nat.cast_add,Nat.cast_one]
      nlinarith only [hCost,hfCost']

#print axioms forkPaschPayment_nonneg
#print axioms weighted_fork_greedy_aux
end TypedTriangle.Pasch

namespace TypedTriangle.CorePaid
open TypedTriangle.Pasch S07V26
variable {V I Ω : Type*} [Fintype V] [Fintype Ω]

/-- Rich covered fork frontend. Both positive modes are literal outputs of
one fork system, and their whole fixed universe is paid before any selector
or later demand is chosen. The physicality assumption is not needed here. -/
theorem forks_on_core_pool_with_pasch_covered (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)}
    (W : Finset V) {κ : ℝ} (hκ : 0 < κ)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I, ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
      κ*Fintype.card V ≤ ((TypedTriangle.commonNbrs H k u v)∩W).card)
    (X P : Finset (Sym2 V)) (hXG : X ⊆ TypedTriangle.edges H) {r b : ℕ}
    (hcov : ∀ e ∈ X, ∃ T, TypedTriangle.IsAllowed H F T ∧ e ∈ TypedTriangle.triEdges T)
    (hX : ∀ v, TypedTriangle.SparseEdge.degIn X v ≤ r) (hP : ∀ v, TypedTriangle.SparseEdge.degIn P v ≤ b)
    (hr : (r:ℝ) ≤ forkEps κ*Fintype.card V) (hb : (b:ℝ) ≤ forkEps κ*Fintype.card V)
    (hn : 32 ≤ κ*Fintype.card V) (R0 : Finset (Finset Ω)) (L0 : ℕ)
    (hR0 : PairCodegreeBound R0 L0) :
    ∃ fk : Sym2 V → Fork V, ForkSystem H.G H.lab F W X P fk ∧
      (∀ v, TypedTriangle.SparseEdge.degIn (forkUnion (XZ X W) fk) v ≤ 2*r+forkQ κ r+4) ∧
      let T := XZ X W
      let Rf := forkUnion T fk
      TypedTriangle.IsDecomposition H F Rf (modeDec fk T ∅) ∧
      TypedTriangle.IsDecomposition H F ((Rf\QU fk T)∪T) (modeDec fk T T) ∧
      PairCodegreeBound (mapConfiguration ι (forkModes T fk)) 2 ∧
      (count (R0∪mapConfiguration ι (forkModes T fk)):ℝ) ≤ count R0+
        (T.card:ℝ)*forkPaschPayment κ L0 (Fintype.card Ω) (Fintype.card V) ∧
      (∀ e ∈ Rf, ∃ v ∈ e, v ∈ W) ∧
      (∀ e ∈ (X\T)∪QU fk T, ∃ v ∈ e, v ∈ W) := by
  obtain ⟨fk,h1,h2,h3,h4,h5,h6,hCost⟩ := weighted_fork_greedy_aux ι W hκ hpool X P hXG
    (fun e he => hcov e (XZ_subset X W he)) hX hP hr hb hn R0 L0 hR0 (XZ X W) (subset_refl _)
  have hFS : ForkSystem H.G H.lab F W X P fk := ⟨h1,h2,h3⟩
  have hMax (v : V) : TypedTriangle.SparseEdge.degIn (forkUnion (XZ X W) fk) v ≤ 2*r+forkQ κ r+4 := by
    by_cases hv : v ∈ W
    · have hh := h5 v hv
      omega
    · have hh := h4 v hv
      have hXv := (S07V26.degIn_mono (XZ_subset X W) v).trans (hX v)
      omega
  have hOff : TypedTriangle.IsDecomposition H F (forkUnion (XZ X W) fk) (modeDec fk (XZ X W) ∅) := by
    have hh := (hFS.fork_modes (I' := ∅) (empty_subset _)).1
    simp only [QU,biUnion_empty,sdiff_empty,union_empty] at hh
    exact hh
  have hOn := (hFS.fork_modes (I' := XZ X W) (subset_refl _)).1
  have hCG := pairCodegreeBound_mapConfiguration ι (forkModes (XZ X W) fk) 2
    (fork_modes_pairCodegree hFS)
  refine ⟨fk,hFS,hMax,hOff,hOn,hCG,hCost,?_,?_⟩
  · intro e he
    obtain ⟨f,hf,he⟩ := mem_biUnion.mp he
    have hValid := (hFS.1 f hf).2
    change e ∈ (fk f).B∪(fk f).Q at he
    rcases mem_union.mp he with he | he
    · exact hValid.B_meets_W e he
    · exact hValid.Q_meets_W e he
  · obtain ⟨_,_,_,_,_,hX1W,_⟩ := hFS.fork_L (L := ∅) (empty_subset _)
    exact hX1W

#print axioms forks_on_core_pool_with_pasch_covered
/-- The legacy physical hypothesis discharges the same covered frontend;
all returned forks, modes and incidence certificates are unchanged. -/
theorem forks_on_core_pool_with_pasch (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)}
    (W : Finset V) {κ : ℝ} (hκ : 0 < κ)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I, ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
      κ*Fintype.card V ≤ ((TypedTriangle.commonNbrs H k u v)∩W).card)
    (X P : Finset (Sym2 V)) (hXG : X ⊆ TypedTriangle.edges H) {r b : ℕ}
    (h2 : IsPhysical H F (TypedTriangle.edges H))
    (hX : ∀ v, TypedTriangle.SparseEdge.degIn X v ≤ r) (hP : ∀ v, TypedTriangle.SparseEdge.degIn P v ≤ b)
    (hr : (r:ℝ) ≤ forkEps κ*Fintype.card V) (hb : (b:ℝ) ≤ forkEps κ*Fintype.card V)
    (hn : 32 ≤ κ*Fintype.card V) (R0 : Finset (Finset Ω)) (L0 : ℕ)
    (hR0 : PairCodegreeBound R0 L0) :
    ∃ fk : Sym2 V → Fork V, ForkSystem H.G H.lab F W X P fk ∧
      (∀ v, TypedTriangle.SparseEdge.degIn (forkUnion (XZ X W) fk) v ≤ 2*r+forkQ κ r+4) ∧
      let T := XZ X W
      let Rf := forkUnion T fk
      TypedTriangle.IsDecomposition H F Rf (modeDec fk T ∅) ∧
      TypedTriangle.IsDecomposition H F ((Rf\QU fk T)∪T) (modeDec fk T T) ∧
      PairCodegreeBound (mapConfiguration ι (forkModes T fk)) 2 ∧
      (count (R0∪mapConfiguration ι (forkModes T fk)):ℝ) ≤ count R0+
        (T.card:ℝ)*forkPaschPayment κ L0 (Fintype.card Ω) (Fintype.card V) ∧
      (∀ e ∈ Rf, ∃ v ∈ e, v ∈ W) ∧
      (∀ e ∈ (X\T)∪QU fk T, ∃ v ∈ e, v ∈ W) := by
  have hCover : EdgeCovered H.G H.lab F := H2Phys.edgeCovered h2
  exact forks_on_core_pool_with_pasch_covered ι W hκ hpool X P hXG
    (fun e he => hCover e (hXG he)) hX hP hr hb hn R0 L0 hR0

#print axioms forks_on_core_pool_with_pasch
end TypedTriangle.CorePaid

end PaschWeightedForkPool

section PaschJointBankRelativeTuplePacking
open Finset Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedStar LocalizedCover

/-- One packing controls the fixed bank and positive linear monitors.
The linear quota is a condition on the monitor, while arbitrary extra tuple
controls remain tied to the same actual clones and packing. No second nibble is used. -/
theorem joint_packing_with_triangle_monitors_pasch_bank_relative_and_tuple_tests
    (C α η τ Λ σ c ε : ℝ) (q L : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η) (hτ : 0 < τ)
    (hΛ : 0 < Λ) (hσ : 0 < σ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (μ : Finset V → ℝ), N ≤ Fintype.card V → IsDiffuseSeed H F C μ →
      CommonNbrCond H F α → ∀ (κ ι ν : Type) [Fintype κ] [Fintype ι] [Fintype ν]
      (bad : κ → Finset V) (loc : κ → Sym2 V → ℝ) (full : ι → Sym2 V → ℝ)
      (w : ν → Finset V → ℝ),
      ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*Λ*(T∩bad k).card) →
      (∀ k T, IsAllowed H F T → |triSum (full k) T| ≤ 3*Λ*T.card) →
      (∀ k T, IsAllowed H F T → |w k T| ≤ 1) →
      ∀ B : Finset (Finset V), PairCodegreeBound B L → (∀ T ∈ B, T.card = 3) →
      ∀ (ξ : Type) [Fintype ξ] (W : ξ → Finset V → ℝ),
      Fintype.card ξ ≤ (Fintype.card V)^q →
      (∀ k T, 0 ≤ W k T ∧ W k T ≤ 1) →
      (∀ k, (∑ T ∈ allowed H F, μ T*W k T) = 0 ∨
        c*Fintype.card V ≤ ∑ T ∈ allowed H F, μ T*W k T) →
      ∀ (ω : Type) [Fintype ω] (Z : ℕ → ω → Finset (Finset V) → ℝ),
      Fintype.card ω ≤ (Fintype.card V)^q →
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ Z ℓ k S) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        (∀ k, |edgeSum (loc k) (edges H\P.biUnion triEdges)| ≤ τ*Fintype.card V*(bad k).card) ∧
        (∀ k, |edgeSum (full k) (edges H\P.biUnion triEdges)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
        (∀ k, |(∑ T ∈ P, w k T)-(∑ T ∈ allowed H F, μ T*w k T)| ≤
          τ*(Fintype.card V:ℝ)^2) ∧
        |(count P:ℝ)-target μ (allowed H F)| ≤ σ*(Fintype.card V:ℝ)^2 ∧
        (∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed H F, μ T*W k T)| ≤
          ε*(∑ T ∈ allowed H F, μ T*W k T)) ∧
        (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 →
          let A := allowed H F
          let n := (Fintype.card V:ℝ)
          let θ := floorWeights A μ n
          |PatternStatistics.statistic (completionWeight B) ℓ P-mixedMass A B θ ℓ| ≤
            (n^2)^(-egj13Epsilon)*(2*(Nat.choose 4 ℓ:ℝ)*target θ A+mixedMass A B θ ℓ)) ∧
        ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k : ω,
          floorTupleTestControl (allowed H F) μ P (Z ℓ k) ℓ := by
  obtain ⟨nJoint,hJoint⟩ := joint_packing_with_triangle_monitors_pasch_and_tuple_tests
    C α η τ Λ σ (q+3) hC hα hη hτ hΛ hσ
  obtain ⟨nNum,hnNum,hNum⟩ := exists_egj13_square_order C c (ε/2) 0 0 hc (by positivity)
  refine ⟨max nJoint (max 2 (max (mixedEligibilityOrder α C L)
    (max nNum ⌈4/c^2⌉₊))),?_⟩
  intro V I _ H F μ hn hH1 hH3 κ ι ν _ _ _ bad loc full w hcard hloc hfull hw B hL hB
    ξ _ W hξ hW hMass ω _ Z hω hZ
  have hn2 : 2 ≤ Fintype.card V := by omega
  have hn1 : 1 ≤ Fintype.card V := by omega
  have hn0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hnNum' : nNum ≤ Fintype.card V := by omega
  obtain ⟨_,_,_,_,_,hρ,hRound,_,hRatio⟩ := hNum (Fintype.card V) hnNum'
  have hSqrt : Real.sqrt (Fintype.card V:ℝ) ≤ c*Fintype.card V/2 := by
    apply sqrt_le_linear_of_order hc hn0
    exact (Nat.le_ceil (4/c^2)).trans (by exact_mod_cast (show ⌈4/c^2⌉₊ ≤ Fintype.card V by omega))
  have hCard' : ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^(q+3) :=
    hcard.trans (pow_le_pow_right₀ (by exact_mod_cast hn1) (by omega))
  have hBaseCard : Fintype.card (Bool ⊕ ξ) ≤ (Fintype.card V)^(q+2) := by
    let n := Fintype.card V
    have hN : n ≤ n^(q+1) := le_self_pow₀ hn1 (by omega)
    have hPower : n^q ≤ n^(q+1) := pow_le_pow_right₀ hn1 (Nat.le_succ q)
    have hξPower : Fintype.card ξ ≤ n^(q+1) := (show Fintype.card ξ ≤ n^q from hξ).trans hPower
    have hTwo : 2 ≤ n^(q+1) := hn2.trans hN
    calc
      Fintype.card (Bool ⊕ ξ) = 2+Fintype.card ξ := by simp
      _ ≤ n^(q+1)+n^(q+1) := Nat.add_le_add hTwo hξPower
      _ = 2*n^(q+1) := by omega
      _ ≤ n*n^(q+1) := Nat.mul_le_mul_right _ hn2
      _ = n^((q+1)+1) := (pow_succ' n (q+1)).symm
      _ = n^(q+2) := congrArg (fun k : ℕ => n^k) (by omega)
  have hExtra : Fintype.card ((Bool ⊕ ξ) ⊕ ω) ≤ (Fintype.card V)^(q+3) := by
    have hω' : Fintype.card ω ≤ (Fintype.card V)^(q+2) :=
      hω.trans (pow_le_pow_right₀ hn1 (by omega))
    calc
      Fintype.card ((Bool ⊕ ξ) ⊕ ω) = Fintype.card (Bool ⊕ ξ)+Fintype.card ω := Fintype.card_sum
      _ ≤ (Fintype.card V)^(q+2)+(Fintype.card V)^(q+2) := Nat.add_le_add hBaseCard hω'
      _ = 2*(Fintype.card V)^(q+2) := by omega
      _ ≤ Fintype.card V*(Fintype.card V)^(q+2) := Nat.mul_le_mul_right _ hn2
      _ = (Fintype.card V)^(q+3) := (pow_succ' _ _).symm
  let A := allowed H F
  let n := (Fintype.card V:ℝ)
  let X : ℕ → (Bool ⊕ ξ) ⊕ ω → Finset (Finset V) → ℝ := fun ℓ =>
    Sum.elim
      (Sum.elim (fun k => paddedFloorWeight A (if k then B else ∅) μ n)
        (fun k => if ℓ = 1 then WeightedClone.linearTupleWeight (W k) else fun _ => 0)) (Z ℓ)
  have hX : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ X ℓ k S := by
    intro ℓ hℓ hℓ4 k S
    rcases k with (k | k) | k
    · exact paddedCompletionWeight_nonneg A (if k then B else ∅) (floorWeights A μ n)
        (fun T _ => floorWeights_nonneg A μ n T) S
    · dsimp only [X,Sum.elim_inl,Sum.elim_inr]
      split_ifs
      · exact sum_nonneg (fun T _ => (hW k T).1)
      · exact le_rfl
    · exact hZ ℓ hℓ hℓ4 k S
  obtain ⟨P,hPsub,hP,hSparse,hLocal,hFull,hTriangles,hPasch,hControls⟩ :=
    hJoint H F μ ((le_max_left _ _).trans hn) hH1 hH3 κ ι ν bad loc full w
      hCard' hloc hfull hw ((Bool ⊕ ξ) ⊕ ω) X hExtra hX
  refine ⟨P,hPsub,hP,hSparse,hLocal,hFull,hTriangles,hPasch,?_,?_,?_⟩
  · intro k
    have hControl : floorTupleTestControl A μ P (WeightedClone.linearTupleWeight (W k)) 1 := by
      simpa [X] using hControls 1 (by omega) (by omega) (Sum.inl (Sum.inr k))
    have hh := relative_error_of_floor_linear_control hH1
      (lt_of_lt_of_le zero_lt_one hC) hc (show 0 ≤ ε/2 by positivity)
      hn0 hRound hSqrt hρ hRatio P (W k) (hW k) (hMass k) hControl
    convert hh using 1 <;> ring
  · intro ℓ hℓ1 hℓ3
    exact mixed_floor_error_of_test_controls hH1 hH3 hα hC L
      (by omega) B P hL hB ℓ hℓ1 hℓ3
      (by simpa [X, A, n] using hControls ℓ hℓ1 (by omega) (Sum.inl (Sum.inl false)))
      (by simpa [X, A, n] using hControls ℓ hℓ1 (by omega) (Sum.inl (Sum.inl true)))
  · intro ℓ hℓ hℓ4 k
    simpa only [X,Sum.elim_inr] using hControls ℓ hℓ hℓ4 (Sum.inr k)

#print axioms joint_packing_with_triangle_monitors_pasch_bank_relative_and_tuple_tests
end TypedTriangle.Pasch

end PaschJointBankRelativeTuplePacking

section PaschAmbientJointTuplePacking
open Finset Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedStar LocalizedCover

/-- The actual normalized ambient monitor is carried by the same packing
as all moments, triangle statistics, pure Pasch, fixed-bank mixed tests and arbitrary extra tuple tests.
Its linear quota is derived from H1/H3, including the empty-host branch. -/
theorem joint_packing_with_triangle_monitors_pasch_bank_ambient_and_tuple_tests
    (C α η τ Λ σ ε : ℝ) (q L : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η) (hτ : 0 < τ)
    (hΛ : 0 < Λ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (μ : Finset V → ℝ), N ≤ Fintype.card V → IsDiffuseSeed H F C μ →
      CommonNbrCond H F α →
      ∀ (X : Type) [Fintype X] (e : V ↪ X) (Rprev : Finset (Finset X)) (Lprev : ℕ),
      PairCodegreeBound Rprev Lprev → ∀ (κ ι ν : Type) [Fintype κ] [Fintype ι] [Fintype ν]
      (bad : κ → Finset V) (loc : κ → Sym2 V → ℝ) (full : ι → Sym2 V → ℝ)
      (w : ν → Finset V → ℝ),
      ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*Λ*(T∩bad k).card) →
      (∀ k T, IsAllowed H F T → |triSum (full k) T| ≤ 3*Λ*T.card) →
      (∀ k T, IsAllowed H F T → |w k T| ≤ 1) →
      ∀ B : Finset (Finset V), PairCodegreeBound B L → (∀ T ∈ B, T.card = 3) →
      ∀ (ω : Type) [Fintype ω] (Y : ℕ → ω → Finset (Finset V) → ℝ),
      Fintype.card ω ≤ (Fintype.card V)^q →
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ Y ℓ k S) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        (∀ k, |edgeSum (loc k) (edges H\P.biUnion triEdges)| ≤ τ*Fintype.card V*(bad k).card) ∧
        (∀ k, |edgeSum (full k) (edges H\P.biUnion triEdges)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
        (∀ k, |(∑ T ∈ P, w k T)-(∑ T ∈ allowed H F, μ T*w k T)| ≤
          τ*(Fintype.card V:ℝ)^2) ∧
        |(count P:ℝ)-target μ (allowed H F)| ≤ σ*(Fintype.card V:ℝ)^2 ∧
        (|(∑ T ∈ P, childPaddedWeight e Rprev Lprev T)-
           (∑ T ∈ allowed H F, μ T*childPaddedWeight e Rprev Lprev T)| ≤
          ε*(∑ T ∈ allowed H F, μ T*childPaddedWeight e Rprev Lprev T)) ∧
        (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 →
          let A := allowed H F
          let n := (Fintype.card V:ℝ)
          let θ := floorWeights A μ n
          |PatternStatistics.statistic (completionWeight B) ℓ P-mixedMass A B θ ℓ| ≤
            (n^2)^(-egj13Epsilon)*(2*(Nat.choose 4 ℓ:ℝ)*target θ A+mixedMass A B θ ℓ)) ∧
        ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k : ω,
          floorTupleTestControl (allowed H F) μ P (Y ℓ k) ℓ := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let c := α^3/(54*C)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨N,hPack⟩ := joint_packing_with_triangle_monitors_pasch_bank_relative_and_tuple_tests
    C α η τ Λ σ c ε q L hC hα hη hτ hΛ hσ hc hε
  refine ⟨max N 1,?_⟩
  intro V I _ H F μ hn hH1 hH3 X _ e Rprev Lprev hPrev
    κ ι ν _ _ _ bad loc full w hcard hloc hfull hw B hL hB ω _ Y hω hY
  have hn1 : 1 ≤ Fintype.card V := by omega
  have hn0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hW : ∀ (_k : Unit) T, 0 ≤ childPaddedWeight e Rprev Lprev T ∧
      childPaddedWeight e Rprev Lprev T ≤ 1 :=
    fun _ T => childPaddedWeight_bounds e Rprev Lprev hPrev hn1 T
  have hQuota : (∑ T ∈ allowed H F, μ T*childPaddedWeight e Rprev Lprev T) = 0 ∨
      c*Fintype.card V ≤ ∑ T ∈ allowed H F, μ T*childPaddedWeight e Rprev Lprev T := by
    rcases child_padded_target_lower_or_empty e Rprev Lprev hPrev hα
      hC0 hn0 hH1 hH3 with hEmpty | hPositive
    · exact Or.inl hEmpty.2
    · exact Or.inr hPositive
  have hUnit : Fintype.card Unit ≤ (Fintype.card V)^q := by
    change 1 ≤ (Fintype.card V)^q
    exact one_le_pow₀ hn1
  obtain ⟨P,hPsub,hP,hSparse,hLocal,hFull,hTriangles,hPasch,hRelative,hMixed,hControls⟩ :=
    hPack H F μ ((le_max_left _ _).trans hn) hH1 hH3 κ ι ν bad loc full w
      hcard hloc hfull hw B hL hB Unit (fun _ => childPaddedWeight e Rprev Lprev)
      hUnit hW (fun _ => hQuota) ω Y hω hY
  exact ⟨P,hPsub,hP,hSparse,hLocal,hFull,hTriangles,hPasch,hRelative (),hMixed,hControls⟩

#print axioms joint_packing_with_triangle_monitors_pasch_bank_ambient_and_tuple_tests
end TypedTriangle.Pasch

end PaschAmbientJointTuplePacking

section PaschProtectedAmbientJointTuplePacking
open Finset Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open ProtectedNibble LocalizedCover

/-- The same protected physical packing retains its original pure targets,
controls mixed fixed-bank interactions, and carries the true ambient padded
monitor with relative precision. Its monitor quota is derived from the actual
residual exact seed and residual H3. That seed is returned before the extra
test family is quantified, so every clone test uses its literal floor. No
extra host hypothesis is imposed by the test-control clause. -/
theorem protected_joint_packing_with_triangle_monitors_pasch_bank_ambient_and_tuple_tests {I : Type} (F : Set (Multiset I))
    (C α η τ L σ εAmbient : ℝ) (h q bankL : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η)
    (hτ : 0 < τ) (hL : 0 < L) (hσ : 0 < σ) (hεAmbient : 0 < εAmbient) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (R : Finset (Sym2 V)) (D : Finset (Finset V)) (d : ℕ),
      n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
      CommonNbrCond H F α → HingeCond H F α h → IsDecomposition H F R D →
      (∀ v, degIn R v ≤ d) → (d:ℝ) ≤ ε*Fintype.card V →
      ∀ (κ ι ν : Type) [Fintype κ] [Fintype ι] [Fintype ν]
        (bad : κ → Finset V) (loc : κ → Sym2 V → ℝ) (full : ι → Sym2 V → ℝ)
        (w : ν → Finset V → ℝ),
        ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^q →
        (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*L*(T∩bad k).card) →
        (∀ k T, IsAllowed H F T → |triSum (full k) T| ≤ 3*L*T.card) →
        (∀ k T, IsAllowed H F T → |w k T| ≤ 1) →
        ∀ B : Finset (Finset V), PairCodegreeBound B bankL → (∀ T ∈ B, T.card = 3) →
        ∀ (X : Type) [Fintype X] (e : V ↪ X) (Rprev : Finset (Finset X)) (Lprev : ℕ),
        PairCodegreeBound Rprev Lprev →
        ∃ ψ : Finset V → ℝ, IsDiffuseSeed (residual H R) F (2*C) ψ ∧
          (∀ T, ψ T ≠ 0 → IsAllowed (residual H R) F T) ∧
          (∀ T, IsAllowed (residual H R) F T →
            |ψ T-φ T| ≤ ExplicitSeed.seedPointwiseCost α C h*d/(Fintype.card V:ℝ)^2) ∧
        ∀ (ω : Type) [Fintype ω] (Yextra : ℕ → ω → Finset (Finset V) → ℝ),
        Fintype.card ω ≤ (Fintype.card V)^q →
        (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ Yextra ℓ k S) →
        ∃ P : Finset (Finset V), IsPacking H F P ∧ Disjoint (P.biUnion triEdges) R ∧
          IsPhysical H F ((edges H\R)\P.biUnion triEdges) ∧
          (∀ v, (((((edges H\R)\P.biUnion triEdges).filter (fun e => v ∈ e)).card):ℝ) ≤ η*Fintype.card V) ∧
          (∀ k, |edgeSum (loc k) ((edges H\R)\P.biUnion triEdges)| ≤ τ*Fintype.card V*(bad k).card) ∧
          (∀ k, |edgeSum (full k) ((edges H\R)\P.biUnion triEdges)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
          (∀ k, |(∑ T ∈ P, w k T)-(∑ T ∈ allowed H F, φ T*w k T)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
          |(count P:ℝ)-target φ (allowed H F)| ≤ σ*(Fintype.card V:ℝ)^2 ∧
          (|(∑ T ∈ P, childPaddedWeight e Rprev Lprev T)-
             (∑ T ∈ allowed (residual H R) F, ψ T*childPaddedWeight e Rprev Lprev T)| ≤
            εAmbient*(∑ T ∈ allowed (residual H R) F, ψ T*childPaddedWeight e Rprev Lprev T)) ∧
          (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 →
            let A := allowed (residual H R) F
            let n := (Fintype.card V:ℝ)
            let θ := floorWeights A ψ n
            |PatternStatistics.statistic (completionWeight B) ℓ P-mixedMass A B θ ℓ| ≤
              (n^2)^(-egj13Epsilon)*(2*(Nat.choose 4 ℓ:ℝ)*target θ A+mixedMass A B θ ℓ)) ∧
          ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k : ω,
            floorTupleTestControl (allowed (residual H R) F) ψ P (Yextra ℓ k) ℓ := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let K := ExplicitSeed.seedPointwiseCost α C h
  have hK : 0 ≤ K := ExplicitSeed.seedPointwiseCost_nonneg h hα hC0
  let δ := targetPaymentBudget C K σ
  have hδ : 0 < δ := targetPaymentBudget_pos hC0 hK hσ
  have hδbounds := targetPaymentBudget_bounds hC0 hK hσ
  let εS := ExplicitSeed.seedExactBudget C α h
  have hεS : 0 < εS := by
    change 0 < RawReference.Explicit.seedBudget (1/C) C α h
    exact RawReference.Explicit.seedBudget_pos h (by positivity)
      (by rw [div_le_iff₀ hC0]; nlinarith only [hC]) hα
  obtain ⟨NP,hPack⟩ := joint_packing_with_triangle_monitors_pasch_bank_ambient_and_tuple_tests
    (2*C) (α/2) η (τ/2) L (σ/2) εAmbient q bankL (by linarith only [hC]) (by positivity)
      hη (by positivity) hL (by positivity) hεAmbient
  let ε := min εS (min (α/4) (min δ (τ/(2*(K+1)))))
  have hε : 0 < ε := lt_min hεS (lt_min (by positivity) (lt_min hδ (by positivity)))
  have hεSeed : ε ≤ εS := min_le_left _ _
  have hεGeometry : ε ≤ α/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hεPasch : ε ≤ δ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεMoment : (K+1)*ε ≤ τ/2 := by
    have hh : ε ≤ τ/(2*(K+1)) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*(K+1))).mp hh
    nlinarith only [hh']
  refine ⟨ε,hε,max (ExplicitSeed.seedExactOrder C) (max NP 1),?_⟩
  intro V _ H φ R D d hn hφ h2 h3 h4 hD hdeg hd κ ι ν _ _ _ bad loc full w hcount hloc hfull hw B hBankL hBank X _ e Rprev Lprev hPrev
  have hnNat : 0 < Fintype.card V := by omega
  have hn0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast hnNat
  have hRsub : R ⊆ edges H := by
    rw [←hD.2.2]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hD.1 T hT) heT
  have hdS : (d:ℝ) ≤ εS*Fintype.card V := hd.trans (mul_le_mul_of_nonneg_right hεSeed hn0.le)
  have hd3 : (d:ℝ) ≤ α/4*Fintype.card V := hd.trans (mul_le_mul_of_nonneg_right hεGeometry hn0.le)
  have hdδ : (d:ℝ) ≤ δ*Fintype.card V := hd.trans (mul_le_mul_of_nonneg_right hεPasch hn0.le)
  obtain ⟨ψ,hψ,hSupp,hClose⟩ := ExplicitSeed.seed_persistence_exact_with_pointwise_bound_explicit
    (F:=F) hC hα h H φ R D d ((le_max_left _ _).trans hn) hφ h4 hRsub hD hdeg hdS
  have hres3 := residual_commonNbrCond h3 R d hdeg hd3
  refine ⟨ψ,hψ,hSupp,hClose,?_⟩
  intro ω _ Yextra hω hExtra
  obtain ⟨P,hPsub,hP,hSparse,hLocal,hGlobal,hTriangles,hPasch,hAmbient,hMixed,hControls⟩ :=
    hPack (residual H R) F ψ ((le_max_left _ _).trans ((le_max_right _ _).trans hn)) hψ hres3 X e Rprev Lprev hPrev
      κ ι ν bad loc full w hcount
      (fun k T hT => hloc k T (isAllowed_mono (subHost_le H _) rfl hT))
      (fun k T hT => hfull k T (isAllowed_mono (subHost_le H _) rfl hT))
      (fun k T hT => hw k T (isAllowed_mono (subHost_le H _) rfl hT)) B hBankL hBank
        ω Yextra hω hExtra
  have hPH : IsPacking H F P := ⟨fun T hT =>
    isAllowed_mono (subHost_le H _) rfl (hP.1 T hT),hP.2⟩
  have hJ : edges (residual H R) = edges H\R := Residual.edges_subHost_eq sdiff_subset
  have hPE : P.biUnion triEdges ⊆ edges H\R := by
    rw [←hJ]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  have hDis : Disjoint (P.biUnion triEdges) R :=
    disjoint_left.mpr fun e he hR => (mem_sdiff.mp (hPE he)).2 hR
  have hPhys := isPhysical_sdiff (isPhysical_sdiff_of_decomposition h2 hD hRsub)
    (isPhysical_of_isDecomposition hPH.isDecomposition) hPE
  have hTransfer := protected_target_transfer hC0 hφ R hRsub K δ (d:ℝ) hK hδ.le hdδ
    hδbounds.1 (fun v => (show (degIn R v:ℝ) ≤ d by exact_mod_cast hdeg v).trans hdδ) hClose hn0
  have hPaid : |target ψ (allowed (residual H R) F)-target φ (allowed H F)| ≤
      (σ/2)*(Fintype.card V:ℝ)^2 := hTransfer.trans
    (mul_le_mul_of_nonneg_right hδbounds.2 (sq_nonneg _))
  have hClose' : ∀ T, IsAllowed (residual H R) F T → |ψ T-φ T| ≤ (K*ε)/Fintype.card V := by
    intro T hT
    calc
      _ ≤ K*d/(Fintype.card V:ℝ)^2 := hClose T hT
      _ ≤ K*(ε*Fintype.card V)/(Fintype.card V:ℝ)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hK) (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt hn0] <;> ring
  have hDegreeε (v : V) : (degIn R v:ℝ) ≤ ε*Fintype.card V :=
    (show (degIn R v:ℝ) ≤ d by exact_mod_cast hdeg v).trans hd
  have hRcard := TriangleMonitors.edge_card_le_of_degree_bound R ε hDegreeε
  refine ⟨P,hPH,hDis,hPhys,?_,?_,?_,?_,?_,hAmbient,hMixed,hControls⟩
  · simpa only [hJ] using hSparse
  · intro k
    exact (show |edgeSum (loc k) ((edges H\R)\P.biUnion triEdges)| ≤
        (τ/2)*Fintype.card V*(bad k).card by simpa only [hJ] using hLocal k).trans
      (by
        have hc : (0:ℝ) ≤ (Fintype.card V:ℝ)*(bad k).card := by positivity
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (show τ/2 ≤ τ by linarith only [hτ]) hc)
  · intro k
    exact (show |edgeSum (full k) ((edges H\R)\P.biUnion triEdges)| ≤
        (τ/2)*(Fintype.card V:ℝ)^2 by simpa only [hJ] using hGlobal k).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hτ]) (sq_nonneg _))
  · intro k
    have hb := TriangleMonitors.triangle_seed_statistic_comparison hC0 hφ R hRsub (K*ε)
      (mul_nonneg hK hε.le) hnNat hClose' (w k) (hw k)
    have hb' : |(∑ T ∈ allowed (residual H R) F, ψ T*w k T)-
        (∑ T ∈ allowed H F, φ T*w k T)| ≤ (τ/2)*(Fintype.card V:ℝ)^2 := by
      calc
        _ ≤ (K*ε)*(Fintype.card V:ℝ)^2+R.card := hb
        _ ≤ (K*ε)*(Fintype.card V:ℝ)^2+ε*(Fintype.card V:ℝ)^2 := add_le_add (le_refl _) hRcard
        _ = ((K+1)*ε)*(Fintype.card V:ℝ)^2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hεMoment (sq_nonneg _)
    calc
      _ ≤ |(∑ T ∈ P, w k T)-(∑ T ∈ allowed (residual H R) F, ψ T*w k T)|+
          |(∑ T ∈ allowed (residual H R) F, ψ T*w k T)-(∑ T ∈ allowed H F, φ T*w k T)| := abs_sub_le _ _ _
      _ ≤ (τ/2)*(Fintype.card V:ℝ)^2+(τ/2)*(Fintype.card V:ℝ)^2 := add_le_add (hTriangles k) hb'
      _ = _ := by ring
  · calc
      _ ≤ |(count P:ℝ)-target ψ (allowed (residual H R) F)|+
          |target ψ (allowed (residual H R) F)-target φ (allowed H F)| := abs_sub_le _ _ _
      _ ≤ (σ/2)*(Fintype.card V:ℝ)^2+(σ/2)*(Fintype.card V:ℝ)^2 := add_le_add hPasch hPaid
      _ = _ := by ring

#print axioms protected_joint_packing_with_triangle_monitors_pasch_bank_ambient_and_tuple_tests
end TypedTriangle.Pasch

end PaschProtectedAmbientJointTuplePacking
