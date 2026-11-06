module
public import RequestProject.TypedTriangle.PaschWeightedForkModes
public import RequestProject.TypedTriangle.PaschAmbientAbsorberCore
public import RequestProject.TypedTriangle.PaschFiniteFamilyIncrement
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V26 S07V25
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I Ω : Type*} [Fintype V] [Fintype Ω]

/-- The existing fork constants leave a positive-density pool; no smaller
sparsity window or larger order is imposed. -/
theorem fork_dense_window {κ n : ℝ} (hκ : 0 < κ) (hn0 : 0 ≤ n) (hn : 32 ≤ κ*n)
    {r b N s : ℕ} (hr : (r:ℝ) ≤ forkEps κ*n) (hb : (b:ℝ) ≤ forkEps κ*n)
    (hN : 2*(N:ℝ) ≤ n*r) (hS : s*forkQ κ r ≤ 8*N) :
    (s:ℝ)+2*((b+3*r+forkQ κ r+3:ℕ):ℝ)+8 ≤ (7/8:ℝ)*κ*n := by
  let Q := forkQ κ r
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast one_le_forkQ κ r
  have hQ0 : (0:ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hQlo := forkQ_lower hκ r
  have hQhi := forkQ_upper hκ r
  let e := forkEps κ
  have he0 : 0 ≤ e := (forkEps_pos hκ).le
  have he : e*(1024*(κ+1)) = κ^2 := by dsimp [e,forkEps]; field_simp
  have hK1 : 1024*e ≤ κ := by
    apply (mul_le_mul_iff_right₀ (show 0 < κ+1 by positivity)).mp
    nlinarith only [he,hκ]
  have hEK : 0 ≤ 1024*e*κ := mul_nonneg (mul_nonneg (by norm_num) he0) hκ.le
  have hK2 : 1024*e ≤ κ^2 := by nlinarith only [he,hEK]
  have hK1N := mul_le_mul_of_nonneg_right hK1 hn0
  have hK2N := mul_le_mul_of_nonneg_right hK2 hn0
  have hB : 8*(N:ℝ) ≤ Q*κ*n/32 := by
    have hh := mul_le_mul_of_nonneg_right hQlo hn0
    nlinarith only [hh,hN]
  have hSR : (s:ℝ)*Q ≤ 8*(N:ℝ) := by exact_mod_cast hS
  have hSbound : (s:ℝ) ≤ κ*n/32 := by
    apply (mul_le_mul_iff_left₀ hQ0).mp
    nlinarith only [hSR,hB]
  have hQκ : (Q:ℝ)*κ ≤ 128*r+κ := by
    have hh := mul_le_mul_of_nonneg_right hQhi hκ.le
    rwa [add_mul,div_mul_cancel₀ _ hκ.ne',one_mul] at hh
  have h3 : 256*(r:ℝ) ≤ κ^2*n/4 := by nlinarith only [hr,hK2N]
  have h2Q : 2*(Q:ℝ) ≤ κ*n/4+2 := by
    apply (mul_le_mul_iff_left₀ hκ).mp
    nlinarith only [hQκ,h3]
  have hbr : 2*(b:ℝ)+6*r ≤ κ*n/128 := by nlinarith only [hr,hb,hK1N]
  change (s:ℝ)+2*((b+3*r+Q+3:ℕ):ℝ)+8 ≤ _
  push_cast
  nlinarith only [hSbound,h2Q,hbr,hn]

private theorem codegree_mono {R : Finset (Finset Ω)} {L K : ℕ}
    (hR : PairCodegreeBound R L) (hLK : L ≤ K) : PairCodegreeBound R K :=
  fun a b hab => (hR a b hab).trans hLK

private theorem codegree_insert (R : Finset (Finset Ω)) (L : ℕ)
    (hR : PairCodegreeBound R L) (T : Finset Ω) : PairCodegreeBound (insert T R) (L+1) := by
  intro a b hab
  have hSub : (insert T R).filter (fun S => a ∈ S ∧ b ∈ S) ⊆
      insert T (R.filter (fun S => a ∈ S ∧ b ∈ S)) := by
    intro S hS
    obtain ⟨hSR,hAS⟩ := mem_filter.mp hS
    rcases mem_insert.mp hSR with rfl | hSR
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_filter.mpr ⟨hSR,hAS⟩)
  exact (card_le_card hSub).trans ((card_insert_le _ _).trans (by have hh := hR a b hab; omega))

private theorem count_insert_le (R : Finset (Finset Ω)) (L : ℕ)
    (hR : PairCodegreeBound R L) (T : Finset Ω) :
    count (insert T R) ≤ count R+rootedCount (insert T R) T := by
  have hh := finite_family_count_increment (fun _ : Unit => T) R L hR
  norm_num [Nat.choose] at hh
  simpa using hh

/-- The old forbidden vertices and two forbidden neighbour sets still
leave enough choices to pay the actual ambient rooted statistic. -/
theorem choose_fork_apex_weighted (ι : V ↪ Ω) (R : Finset (Finset Ω)) (L : ℕ)
    (hR : PairCodegreeBound R L) (p q : V) (A S N1 N2 : Finset V) {κ : ℝ}
    (hκ : 0 < κ) (hn : 0 < (Fintype.card V:ℝ))
    (hA : κ*Fintype.card V ≤ A.card)
    (hBad : (S.card:ℝ)+N1.card+N2.card ≤ (7/8:ℝ)*κ*Fintype.card V) :
    ∃ x ∈ A, x ∉ S ∧ x ∉ N1 ∧ x ∉ N2 ∧
      (rootedCount (insert {ι p,ι q,ι x} R) {ι p,ι q,ι x}:ℝ) ≤
        Ambient.orderRatio ι*(L:ℝ)^3/(κ/8) := by
  let bad := S∪N1∪N2
  let good := A\bad
  have hBadCard : (bad.card:ℝ) ≤ S.card+N1.card+N2.card := by
    dsimp only [bad]
    exact_mod_cast (card_union_le (S∪N1) N2).trans
      (Nat.add_le_add_right (card_union_le S N1) _)
  have hCover : (A.card:ℝ) ≤ good.card+bad.card := by
    exact_mod_cast (card_le_card (show A ⊆ good∪bad from fun x hx => by
      by_cases hb : x ∈ bad
      · exact mem_union_right _ hb
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hx,hb⟩))).trans (card_union_le _ _)
  have hGood : (κ/8)*Fintype.card V ≤ good.card := by linarith only [hA,hBad,hBadCard,hCover]
  obtain ⟨x,hx,hCost⟩ := Ambient.exists_apex_total_cost_in_pool ι R L hR
    (fun _ : Unit => p) (fun _ : Unit => q) good (κ/8) (by positivity) hn hGood
  obtain ⟨hxA,hxBad⟩ := mem_sdiff.mp hx
  have hxS : x ∉ S := fun hh => hxBad (mem_union_left _ (mem_union_left _ hh))
  have hxN1 : x ∉ N1 := fun hh => hxBad (mem_union_left _ (mem_union_right _ hh))
  have hxN2 : x ∉ N2 := fun hh => hxBad (mem_union_right _ hh)
  exact ⟨x,hxA,hxS,hxN1,hxN2,by simpa using hCost⟩


/-- Three actual H3 choices build the old fork and pay its entire fixed
mode universe by telescoping against R0, T0 and T1 in that order. -/
theorem weighted_fork_step (ι : V ↪ Ω) (G : SimpleGraph V) (lab : V → I)
    (F : Set (Multiset I)) (W : Finset V) {κ : ℝ} (hκ : 0 < κ)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I, ({lab u,lab v,k}:Multiset I) ∈ F →
      κ*Fintype.card V ≤ ((SparseEdge.commonNbrs G lab k u v)∩W).card)
    {U : Finset (Sym2 V)} {S : Finset V} {D : ℕ} (hU : ∀ x, SparseEdge.degIn U x ≤ D)
    (hwin : (S.card:ℝ)+2*D+8 ≤ (7/8:ℝ)*κ*Fintype.card V)
    {u v c : V} (huW : u ∉ W) (hvW : v ∉ W) (hadj : (link G lab F u).Adj v c)
    (R0 : Finset (Finset Ω)) (L : ℕ) (hR0 : PairCodegreeBound R0 L) :
    ∃ f : Fork V, f.u = u ∧ f.v = v ∧ f.Valid G lab F W ∧ Disjoint f.E U ∧
      f.w ∉ S ∧ f.a ∉ S ∧ f.b ∉ S ∧
      (count (R0∪mapConfiguration ι {f.T0,f.T1,f.T2}):ℝ) ≤
        count R0+3*(Ambient.orderRatio ι*((L+2:ℕ):ℝ)^3/(κ/8)) := by
  obtain ⟨huv, hF⟩ := link_root_ne hadj
  have hnNat : 0 < Fintype.card V := by
    have hh : 3 ≤ Fintype.card V := hadj.2.1 ▸ card_le_univ ({u,v,c}:Finset V)
    omega
  have hn : 0 < (Fintype.card V:ℝ) := by exact_mod_cast hnNat
  let pay := Ambient.orderRatio ι*((L+2:ℕ):ℝ)^3/(κ/8)
  have hRL : PairCodegreeBound R0 (L+2) := codegree_mono hR0 (by omega)
  have hN : ∀ (U' : Finset (Sym2 V)) x, (SparseEdge.nbrIn U' x).card ≤ SparseEdge.degIn U' x := SparseEdge.card_nbrIn_le
  -- choice of `w`
  obtain ⟨w,hwA,hwS,hwU,hwV,hwCost⟩ := choose_fork_apex_weighted ι R0 (L+2) hRL u v
    ((SparseEdge.commonNbrs G lab (lab c) u v)∩W) S (SparseEdge.nbrIn U u) (SparseEdge.nbrIn U v) hκ hn
    (hpool u v huv _ hF) (by
      have h1 := (hN U u).trans (hU u)
      have h2 := (hN U v).trans (hU v)
      have hh : (S.card:ℝ)+(SparseEdge.nbrIn U u).card+(SparseEdge.nbrIn U v).card ≤ S.card+2*D+8 := by
        exact_mod_cast (show S.card+(SparseEdge.nbrIn U u).card+(SparseEdge.nbrIn U v).card ≤ S.card+2*D+8 by omega)
      exact hh.trans hwin)
  let T0m : Finset Ω := {ι u,ι v,ι w}
  let R1 := insert T0m R0
  have hR1 : PairCodegreeBound R1 (L+1) := codegree_insert R0 L hR0 T0m
  have hR1L : PairCodegreeBound R1 (L+2) := codegree_mono hR1 (by omega)
  obtain ⟨hwc, hwW⟩ := mem_inter.1 hwA
  have h0 : (link G lab F u).Adj v w := commonNbr_link_adj hadj hwc
  obtain ⟨huw, hF2⟩ := link_root_ne h0.symm
  set U1 := insert s(u, w) (insert s(v, w) U) with hU1
  have hU1d : ∀ x, SparseEdge.degIn U1 x ≤ D + 2 := fun x =>
    (degIn_insert_le _ _ x).trans (by have := (degIn_insert_le s(v, w) U x); have := hU x; omega)
  -- choice of `a`
  obtain ⟨a,haA,haS,haU,haW',haCost⟩ := choose_fork_apex_weighted ι R1 (L+2) hR1L u w
    ((SparseEdge.commonNbrs G lab (lab v) u w)∩W) S (SparseEdge.nbrIn U1 u) (SparseEdge.nbrIn U1 w) hκ hn
    (hpool u w huw _ hF2) (by
      have h1 := (hN U1 u).trans (hU1d u)
      have h2 := (hN U1 w).trans (hU1d w)
      have hh : (S.card:ℝ)+(SparseEdge.nbrIn U1 u).card+(SparseEdge.nbrIn U1 w).card ≤ S.card+2*D+8 := by
        exact_mod_cast (show S.card+(SparseEdge.nbrIn U1 u).card+(SparseEdge.nbrIn U1 w).card ≤ S.card+2*D+8 by omega)
      exact hh.trans hwin)
  let T1m : Finset Ω := {ι u,ι w,ι a}
  let R2 := insert T1m R1
  have hR2 : PairCodegreeBound R2 (L+2) := codegree_insert R1 (L+1) hR1 T1m
  obtain ⟨hac, haW⟩ := mem_inter.1 haA
  have h1 : (link G lab F u).Adj w a := commonNbr_link_adj h0.symm hac
  have h0' : (link G lab F v).Adj u w := ⟨huw, by rw [Finset.insert_comm]; exact h0.2⟩
  obtain ⟨hvw, hF3⟩ := link_root_ne h0'.symm
  set U2 := insert s(u, a) (insert s(a, w) U1) with hU2
  have hU2d : ∀ x, SparseEdge.degIn U2 x ≤ D + 4 := fun x =>
    (degIn_insert_le _ _ x).trans
      (by have := (degIn_insert_le s(a, w) U1 x); have := hU1d x; omega)
  -- choice of `b`
  obtain ⟨b,hbA,hbS,hbU,hbW',hbCost⟩ := choose_fork_apex_weighted ι R2 (L+2) hR2 v w
    ((SparseEdge.commonNbrs G lab (lab u) v w)∩W) S (SparseEdge.nbrIn U2 v) (SparseEdge.nbrIn U2 w) hκ hn
    (hpool v w hvw _ hF3) (by
      have h1 := (hN U2 v).trans (hU2d v)
      have h2 := (hN U2 w).trans (hU2d w)
      have hh : (S.card:ℝ)+(SparseEdge.nbrIn U2 v).card+(SparseEdge.nbrIn U2 w).card ≤ S.card+2*D+8 := by
        exact_mod_cast (show S.card+(SparseEdge.nbrIn U2 v).card+(SparseEdge.nbrIn U2 w).card ≤ S.card+2*D+8 by omega)
      exact hh.trans hwin)
  let T2m : Finset Ω := {ι v,ι w,ι b}
  let R3 := insert T2m R2
  obtain ⟨hbc, hbW⟩ := mem_inter.1 hbA
  have h2 : (link G lab F v).Adj w b := commonNbr_link_adj h0'.symm hbc
  rw [S07V26.mem_nbrIn] at hwU hwV haU haW' hbU hbW'
  have hab : a ≠ b := by
    rintro rfl
    exact hbW' (by rw [Sym2.eq_swap]; exact mem_insert_of_mem (mem_insert_self _ _))
  refine ⟨⟨u, v, w, a, b⟩, rfl, rfl, ⟨huW, hvW, hwW, haW, hbW, hab, h0.2, h1.2, h2.2⟩, ?_,
    hwS, haS, hbS, ?_⟩
  rw [Finset.disjoint_left]
  intro e he heU
  rw [Fork.mem_E] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at heU
  · exact hwU heU
  · exact hwV heU
  · exact haU (mem_insert_of_mem (mem_insert_of_mem heU))
  · exact haW' (by rw [Sym2.eq_swap]; exact mem_insert_of_mem (mem_insert_of_mem heU))
  · exact hbW' (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem
      (mem_insert_of_mem heU))))
  · exact hbU (by
      rw [Sym2.eq_swap]
      exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem heU))))
  · change (count (R0∪mapConfiguration ι {{u,v,w},{u,w,a},{v,w,b}}):ℝ) ≤ _
    have hSets : R0∪mapConfiguration ι {{u,v,w},{u,w,a},{v,w,b}} = R3 := by
      dsimp only [R3,R2,R1,T0m,T1m,T2m]
      simp only [mapConfiguration,map_insert,map_singleton]
      change R0 ∪ {({u,v,w}:Finset V).map ι,({u,w,a}:Finset V).map ι,
        ({v,w,b}:Finset V).map ι} = _
      simp only [map_insert,map_singleton]
      ext T
      simp only [mem_union,mem_insert,mem_singleton]
      tauto
    rw [hSets]
    have hc0 : (count R1:ℝ) ≤ count R0+(rootedCount R1 T0m:ℝ) := by
      exact_mod_cast count_insert_le R0 L hR0 T0m
    have hc1 : (count R2:ℝ) ≤ count R1+(rootedCount R2 T1m:ℝ) := by
      exact_mod_cast count_insert_le R1 (L+1) hR1 T1m
    have hc2 : (count R3:ℝ) ≤ count R2+(rootedCount R3 T2m:ℝ) := by
      exact_mod_cast count_insert_le R2 (L+2) hR2 T2m
    change (rootedCount R1 T0m:ℝ) ≤ pay at hwCost
    change (rootedCount R2 T1m:ℝ) ≤ pay at haCost
    change (rootedCount R3 T2m:ℝ) ≤ pay at hbCost
    change (count R3:ℝ) ≤ count R0+3*pay
    linarith only [hc0,hc1,hc2,hwCost,haCost,hbCost]

#print axioms fork_dense_window
#print axioms choose_fork_apex_weighted
#print axioms weighted_fork_step
end TypedTriangle.Pasch
