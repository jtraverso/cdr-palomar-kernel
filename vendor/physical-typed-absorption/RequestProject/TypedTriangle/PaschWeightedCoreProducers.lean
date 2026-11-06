module
public import RequestProject.TypedTriangle.PaschWeightedRoutedSelectors
public import RequestProject.TypedTriangle.PaschWeightedCoreAvailability
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SimpleGraph SelBridge SelTyped SelSubdiv SelRoute ParitySel SelBalanced SelEmbed SelSimul S07V27
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I Ambient : Type} [Fintype V] [Fintype Ambient] [DecidableEq V] [DecidableEq Ambient]

def weightedCoreRoutePay (a : ℝ) (m nAmbient nWindow : ℕ) (L : ℕ) : ℝ :=
  200*ambientWeightedRoutePayment a m (L+60) nAmbient nWindow

theorem weightedCoreRoutePay_nonneg (a : ℝ) (ha : 0  <  a)
    (m nAmbient nWindow L : ℕ) : 0 ≤ weightedCoreRoutePay a m nAmbient nWindow L := by
  unfold weightedCoreRoutePay ambientWeightedRoutePayment
  positivity

theorem weighted_coreAvail_par (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (U K Wc : Finset V) {A ζw ρw m : ℕ} (hm : 0  <  m) (hOdd : Odd (m+1)) (hA : 4 * ((m+1) - 1) + 2 ≤ A)
    (hUK : U ⊆ K) (hK : ζw + 3 * U.card ≤ K.card) (hKW : K ⊆ Wc ∪ U)
    (hKwing : ∀ a ∈ K, G.Adj v a)
    (ι : V ↪ Ambient) (a q : ℝ) (ha : 0  <  a) (hq : 0  <  q)
    (hOrder : 2 ≤ q*Fintype.card V)
    (hWindow : (Wc.card:ℝ) ≤ 2*q*Fintype.card V)
    (hWindowLower : q*Fintype.card V/4 ≤ (Wc.card:ℝ))
    (hPaths : ∀x y, ParAllowed K x y →
      a*(Fintype.card V:ℝ)^m*q^m/4 ≤ (S07V24.pathsIn (typedLink G lab F v) m x y Wc).card)
    (hBudget : ((ζw+3*U.card+m*(4*U.card):ℕ):ℝ) ≤
      Vortex.windowRouteRate a q m*Fintype.card V)
    (hρ : (ρw:ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V) :
    WeightedCoreAvail G lab F v U (fun S => Even S.card) A ζw ρw Wc ι
      (weightedCoreRoutePay a m (Fintype.card Ambient) Wc.card) := by
  intro R0 L0 hR0 Z0 Bf hZ0 hBf
  let H := typedLink G lab F v
  have hHle : H ≤ typedLink G lab F v := le_rfl
  set r := U.card with hr
  let e := U.equivFin
  let ψ : Fin r → V := fun i => (e.symm i : V)
  have hψ : Function.Injective ψ := fun i j h => e.symm.injective (Subtype.ext h)
  have hψU : ∀ i, ψ i ∈ U := fun i => (e.symm i).2
  have hψsurj : ∀ u ∈ U, ∃ i, ψ i = u := fun u hu => ⟨e ⟨u, hu⟩, by simp [ψ]⟩
  have hZ0' : (Z0 \ U).card ≤ ζw := (card_le_card sdiff_subset).trans hZ0
  have hZBudget : (((Z0\U).card+3*r+m*(4*r):ℕ):ℝ) ≤
      Vortex.windowRouteRate a q m*Fintype.card V := by
    have hNat : (Z0\U).card+3*r+m*(4*r) ≤ ζw+3*U.card+m*(4*U.card) := by
      dsimp only [r]
      omega
    exact (Nat.cast_le.mpr hNat).trans hBudget
  have hBad : ∀y, (S07V27.bfGraph Bf).degree y ≤ ρw :=
    fun y => (S07V27.bfGraph_degree_le Bf y).trans (hBf y)
  obtain ⟨Dt,hφP,hφC,hZ,hZi,_,_,_,hW,_,hdeg,hpe,hwing,hCount,hWin,hAvoid,hmodes⟩ :=
    weighted_parity_selector_routed G lab F v H hHle K (Z0\U) r m hm hOdd
      hKwing ψ hψ (fun i => hUK (hψU i))
      (fun i h => (mem_sdiff.mp h).2 (hψU i))
      (fun _ => K) (fun _ => subset_refl _)
      (fun _ => by show _ ≤ K.card; omega)
      ι Wc a q ha hq hOrder hWindow hWindowLower hPaths
      (S07V27.bfGraph Bf) ρw hBad hρ hZBudget R0 L0 hR0
  choose Fm hFm using hmodes
  let pre : Finset V → Finset (Fin r) := fun S => univ.filter (fun i => ψ i ∈ S)
  have hpre : ∀ S ⊆ U, (pre S).image ψ = S := by
    intro S hS
    ext y
    simp only [pre, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hy
      obtain ⟨i, rfl⟩ := hψsurj y (hS hy)
      exact ⟨i, hy, rfl⟩
  set W := (auxSet r).image Dt.φ ∪ Dt.internals with hWdef
  -- auxiliary images are not ports
  have haux_notU : ∀ x ∈ auxSet r, Dt.φ x ∉ U := by
    intro x hx hU
    obtain ⟨i, hi⟩ := hψsurj _ hU
    rw [← hφP i] at hi
    have := Dt.φ_inj hi
    subst this
    simp [auxSet] at hx
  have hWU : Disjoint W U := by
    rw [Finset.disjoint_left]
    intro y hy hyU
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      exact haux_notU x hx hyU
    · obtain ⟨i, rfl⟩ := hψsurj y hyU
      rw [← hφP i] at hy
      exact OddSubdivision.φ_not_mem_internals _ hy
  refine ⟨⟨W, Dt.pathEdges, fun S =>
    if h : Even (pre S).card then Dt.modeEdges (Fm (pre S) h) else ∅⟩, ?_, ?_, ?_⟩
  refine
    { typed := fun f hf => ?_
      avoidB := ?_
      supp := fun f hf y hy => ?_
      wing := hwing
      avoidZ := ?_
      portFree := hWU
      card_le := ?_
      deg_le := fun y => (hdeg y).trans (by norm_num)
      modes := fun S hS hev => ?_ }
  · obtain ⟨x, y, rfl, -, hT⟩ := hpe f hf
    exact ⟨x, y, rfl, hT⟩
  · rw [Finset.disjoint_left]
    intro f hf hfB
    obtain ⟨x, y, rfl, hH, hT⟩ := hpe f hf
    obtain ⟨a,b,heq,hNo⟩ := hAvoid s(x,y) hf
    have hNotDiag : ¬ (s(x,y):Sym2 V).IsDiag := by
      simpa only [Sym2.mk_isDiag_iff] using hT.1
    have hab : a≠b := by
      intro he
      apply hNotDiag
      rw [heq,he]
      exact Sym2.mk_isDiag_iff.mpr rfl
    apply hNo
    exact S07V27.bfGraph_adj.mpr ⟨by rwa [←heq],hab⟩
  · obtain ⟨e', he', j, hj, rfl⟩ := (OddSubdivision.mem_pathEdges _).mp hf
    rcases OddSubdivision.mem_pe_cases e' hj hy with ⟨x, rfl⟩ | ⟨k, hk1, hk2, rfl⟩
    · rcases x with i | x
      · left; rw [show (Sum.inl i : PV r) = pu i from rfl, hφP i]; exact hψU i
      · right
        exact mem_union_left _ (mem_image.mpr ⟨Sum.inr x, by simp [auxSet], rfl⟩)
    · right
      exact mem_union_right _ ((OddSubdivision.mem_internals _).mpr ⟨e', he', k, hk1, hk2, rfl⟩)
  · rw [Finset.disjoint_left]
    intro y hy hyZ
    have hyZ' : y ∈ Z0 \ U := mem_sdiff.mpr ⟨hyZ, Finset.disjoint_left.mp hWU hy⟩
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨x, -, rfl⟩ := mem_image.mp hy
      exact hZ x hyZ'
    · exact hZi y hy hyZ'
  · refine hW.trans ?_
    calc 2 * r + ((m+1) - 1) * (4 * r) = (4 * ((m+1) - 1) + 2) * r := by ring
      _ ≤ A * r := Nat.mul_le_mul_right _ hA
  · have hcard : (pre S).card = S.card := by
      conv_rhs => rw [← hpre S hS]
      rw [card_image_of_injective _ hψ]
    have hev' : Even (pre S).card := hcard ▸ hev
    simp only [dif_pos hev']
    have := (hFm (pre S) hev').2.1
    rwa [par_portset_image' hφP, hpre S hS] at this
  · intro y hy
    have hyU : y ∉ U := Finset.disjoint_left.mp hWU hy
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      exact (mem_union.mp (hKW (hφC x hx))).resolve_right hyU
    · exact hWin hy

  · have hPay : 0 ≤ ambientWeightedRoutePayment a m (L0+60) (Fintype.card Ambient) Wc.card := by
      have hp : 0 ≤ 200*ambientWeightedRoutePayment a m (L0+60) (Fintype.card Ambient) Wc.card :=
        weightedCoreRoutePay_nonneg a ha m _ _ L0
      linarith only [hp]
    have hCoeff : ((paritySelector r).edgeFinset.card:ℝ) ≤ 200*(U.card:ℝ) := by
      have hh := paritySelector_card_edgeFinset_le r
      dsimp only [r] at hh
      exact_mod_cast hh.trans (Nat.mul_le_mul_right U.card (by norm_num : 4 ≤ 200))
    have hMult := mul_le_mul_of_nonneg_right hCoeff hPay
    change (count (R0∪mapConfiguration ι (Dt.pathEdges.image (selectorTriangle v))):ℝ) ≤ _
    dsimp only [weightedCoreRoutePay]
    nlinarith only [hCount,hMult]

theorem weighted_coreAvail_bal (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (U K Xs Ys Wc : Finset V) {A ζw ρw m : ℕ} (hm : 0  <  m) (hOdd : Odd (m+1)) (hU : U.Nonempty)
    (hA : 200 * ((m+1) - 1) + 8 ≤ A)
    (hXK : Xs ⊆ K) (hYK : Ys ⊆ K) (hXY : Disjoint Xs Ys) (hUXY : U ⊆ Xs ∪ Ys)
    (hXc : ζw + 10 * U.card ≤ Xs.card) (hYc : ζw + 10 * U.card ≤ Ys.card)
    (hKW : K ⊆ Wc ∪ U) (hKwing : ∀ a ∈ K, G.Adj v a)
    (ι : V ↪ Ambient) (a q : ℝ) (ha : 0  <  a) (hq : 0  <  q)
    (hOrder : 2 ≤ q*Fintype.card V)
    (hWindow : (Wc.card:ℝ) ≤ 2*q*Fintype.card V)
    (hWindowLower : q*Fintype.card V/4 ≤ (Wc.card:ℝ))
    (hPaths : ∀ x y, BalAllowed Xs Ys x y →
      a*(Fintype.card V:ℝ)^m*q^m/4 ≤ (S07V24.pathsIn (typedLink G lab F v) m x y Wc).card)
    (hBudget : ((ζw+10*U.card+m*(200*U.card):ℕ):ℝ) ≤
      Vortex.windowRouteRate a q m*Fintype.card V)
    (hρ : (ρw:ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V) :
    WeightedCoreAvail G lab F v U (fun S => (S ∩ Xs).card = (S ∩ Ys).card) A ζw ρw Wc ι
      (weightedCoreRoutePay a m (Fintype.card Ambient) Wc.card) := by
  intro R0 L0 hR0 Z0 Bf hZ0 hBf
  let H := typedLink G lab F v
  have hHle : H ≤ typedLink G lab F v := le_rfl
  set UL := U ∩ Xs with hUL
  set UR := U ∩ Ys with hUR
  set l := UL.card with hl
  set r := UR.card with hr
  have hUsplit : U = UL ∪ UR := by
    ext y; simp only [hUL, hUR, mem_union, mem_inter]
    constructor
    · intro hy; rcases mem_union.mp (hUXY hy) with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
  have hlr : l + r = U.card := by
    rw [hUsplit, card_union_of_disjoint (disjoint_of_subset_left inter_subset_right
      (disjoint_of_subset_right inter_subset_right hXY))]
  have hk : 1 ≤ max l r := by
    have := hU.card_pos; omega
  have hkU : max l r ≤ U.card := by omega
  let eL := UL.equivFin
  let eR := UR.equivFin
  let ψL : Fin l → V := fun i => (eL.symm i : V)
  let ψR : Fin r → V := fun i => (eR.symm i : V)
  have hψL : Function.Injective ψL := fun i j h => eL.symm.injective (Subtype.ext h)
  have hψR : Function.Injective ψR := fun i j h => eR.symm.injective (Subtype.ext h)
  have hψLU : ∀ i, ψL i ∈ UL := fun i => (eL.symm i).2
  have hψRU : ∀ i, ψR i ∈ UR := fun i => (eR.symm i).2
  have hψLs : ∀ u ∈ UL, ∃ i, ψL i = u := fun u hu => ⟨eL ⟨u, hu⟩, by simp [ψL]⟩
  have hψRs : ∀ u ∈ UR, ∃ i, ψR i = u := fun u hu => ⟨eR ⟨u, hu⟩, by simp [ψR]⟩
  have hZ0' : (Z0 \ U).card ≤ ζw := (card_le_card sdiff_subset).trans hZ0
  have hMk : (((Z0 \ U).card+10*max l r+m*(200*max l r):ℕ):ℝ) ≤
      Vortex.windowRouteRate a q m*Fintype.card V := by
    have hNat : (Z0 \ U).card+10*max l r+m*(200*max l r) ≤
        ζw+10*U.card+m*(200*U.card) := by
      have hMult := Nat.mul_le_mul_left m (Nat.mul_le_mul_left 200 hkU)
      omega
    exact (Nat.cast_le.mpr hNat).trans hBudget
  have hBad : ∀ y, (S07V27.bfGraph Bf).degree y ≤ ρw :=
    fun y => (S07V27.bfGraph_degree_le Bf y).trans (hBf y)
  obtain ⟨QB,_,_,hQBcard,Dt,hφL,hφR,_,hφS,hZ,hZi,_,_,_,hW,_,hdeg,hpe,hwing,
      hCount,hWin,hAvoid,hmodes⟩ :=
    weighted_balanced_selector_routed l r hk G lab F v H hHle K Xs Ys (Z0 \ U)
      m hm hOdd hKwing hXK hYK hXY ψL ψR hψL hψR
      (fun i => (mem_inter.mp (hψLU i)).2) (fun i => (mem_inter.mp (hψRU i)).2)
      (fun i h => (mem_sdiff.mp h).2 (mem_inter.mp (hψLU i)).1)
      (fun i h => (mem_sdiff.mp h).2 (mem_inter.mp (hψRU i)).1)
      (Sum.elim (fun _ => Xs) (fun _ => Ys))
      (fun x hx => by
        cases x with
        | inl _ => exact subset_refl _
        | inr _ => simp at hx)
      (fun x hx => by
        cases x with
        | inl _ => simp at hx
        | inr _ => exact subset_refl _)
      (fun x => by
        have : (Z0 \ U).card + 10 * max l r ≤ ζw + 10 * U.card := by omega
        cases x with
        | inl _ => show _ ≤ Xs.card; omega
        | inr _ => show _ ≤ Ys.card; omega)
      ι Wc a q ha hq hOrder hWindow hWindowLower hPaths
      (S07V27.bfGraph Bf) ρw hBad hρ hMk R0 L0 hR0
  choose Fm hFm using hmodes
  let preL : Finset V → Finset (Fin l) := fun S => univ.filter (fun i => ψL i ∈ S)
  let preR : Finset V → Finset (Fin r) := fun S => univ.filter (fun i => ψR i ∈ S)
  have hpreL : ∀ S ⊆ U, (preL S).image ψL = S ∩ Xs := by
    intro S hS
    ext y
    simp only [preL, mem_image, mem_filter, mem_univ, true_and, mem_inter]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨hi, (mem_inter.mp (hψLU i)).2⟩
    · rintro ⟨hy, hyX⟩
      obtain ⟨i, rfl⟩ := hψLs y (mem_inter.mpr ⟨hS hy, hyX⟩)
      exact ⟨i, hy, rfl⟩
  have hpreR : ∀ S ⊆ U, (preR S).image ψR = S ∩ Ys := by
    intro S hS
    ext y
    simp only [preR, mem_image, mem_filter, mem_univ, true_and, mem_inter]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨hi, (mem_inter.mp (hψRU i)).2⟩
    · rintro ⟨hy, hyY⟩
      obtain ⟨i, rfl⟩ := hψRs y (mem_inter.mpr ⟨hS hy, hyY⟩)
      exact ⟨i, hy, rfl⟩
  set W := (OddSubdivision.auxB l r).image Dt.φ ∪ Dt.internals with hWdef
  have hport : ∀ x : BV l r, x ∉ OddSubdivision.auxB l r →
      (∃ p, x = Sum.inl (Sum.inr p)) ∨ ∃ q, x = Sum.inr (Sum.inr q) := by
    intro x hx
    rcases x with (a | p) | (b | q)
    · exact absurd (by simp [OddSubdivision.auxB]) hx
    · exact Or.inl ⟨p, rfl⟩
    · exact absurd (by simp [OddSubdivision.auxB]) hx
    · exact Or.inr ⟨q, rfl⟩
  have hUimg : ∀ u ∈ U, (∃ p, Dt.φ (Sum.inl (Sum.inr p)) = u) ∨
      ∃ q, Dt.φ (Sum.inr (Sum.inr q)) = u := by
    intro u hu
    rw [hUsplit] at hu
    rcases mem_union.mp hu with hu | hu
    · obtain ⟨p, rfl⟩ := hψLs u hu; exact Or.inl ⟨p, hφL p⟩
    · obtain ⟨q, rfl⟩ := hψRs u hu; exact Or.inr ⟨q, hφR q⟩
  have hWU : Disjoint W U := by
    rw [Finset.disjoint_left]
    intro y hy hyU
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      rcases hUimg _ hyU with ⟨p, hp⟩ | ⟨q, hq⟩
      · have := Dt.φ_inj hp; subst this
        exact Finset.disjoint_left.mp (OddSubdivision.portsB_disjoint univ univ)
          (by simp [OddSubdivision.portsB]) hx
      · have := Dt.φ_inj hq; subst this
        exact Finset.disjoint_left.mp (OddSubdivision.portsB_disjoint univ univ)
          (by simp [OddSubdivision.portsB]) hx
    · rcases hUimg _ hyU with ⟨p, hp⟩ | ⟨q, hq⟩
      · rw [← hp] at hy; exact OddSubdivision.φ_not_mem_internals _ hy
      · rw [← hq] at hy; exact OddSubdivision.φ_not_mem_internals _ hy
  refine ⟨⟨W, Dt.pathEdges, fun S =>
    if h : (preL S).card = (preR S).card then Dt.modeEdges (Fm (preL S) (preR S) h)
    else ∅⟩, ?_, ?_, ?_⟩
  refine
    { typed := fun f hf => ?_
      avoidB := ?_
      supp := fun f hf y hy => ?_
      wing := hwing
      avoidZ := ?_
      portFree := hWU
      card_le := ?_
      deg_le := hdeg
      modes := fun S hS hbal => ?_ }
  · obtain ⟨x, y, rfl, -, hT⟩ := hpe f hf
    exact ⟨x, y, rfl, hT⟩
  · rw [Finset.disjoint_left]
    intro f hf hfB
    obtain ⟨x, y, rfl, hH, hT⟩ := hpe f hf
    obtain ⟨a,b,heq,hNo⟩ := hAvoid s(x,y) hf
    have hNotDiag : ¬ (s(x,y):Sym2 V).IsDiag := by
      simpa only [Sym2.mk_isDiag_iff] using hT.1
    have hab : a ≠ b := by
      intro he
      apply hNotDiag
      rw [heq,he]
      exact Sym2.mk_isDiag_iff.mpr rfl
    apply hNo
    exact S07V27.bfGraph_adj.mpr ⟨by rwa [←heq],hab⟩
  · obtain ⟨e', he', j, hj, rfl⟩ := (OddSubdivision.mem_pathEdges _).mp hf
    rcases OddSubdivision.mem_pe_cases e' hj hy with ⟨x, rfl⟩ | ⟨k, hk1, hk2, rfl⟩
    · by_cases hx : x ∈ OddSubdivision.auxB l r
      · exact Or.inr (mem_union_left _ (mem_image_of_mem _ hx))
      · left
        rcases hport x hx with ⟨p, rfl⟩ | ⟨q, rfl⟩
        · rw [hφL p]; exact (mem_inter.mp (hψLU p)).1
        · rw [hφR q]; exact (mem_inter.mp (hψRU q)).1
    · right
      exact mem_union_right _ ((OddSubdivision.mem_internals _).mpr ⟨e', he', k, hk1, hk2, rfl⟩)
  · rw [Finset.disjoint_left]
    intro y hy hyZ
    have hyZ' : y ∈ Z0 \ U := mem_sdiff.mpr ⟨hyZ, Finset.disjoint_left.mp hWU hy⟩
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨x, -, rfl⟩ := mem_image.mp hy
      exact hZ x hyZ'
    · exact hZi y hy hyZ'
  · refine hW.trans ?_
    calc 8 * max l r + ((m+1) - 1) * (200 * max l r) = (200 * ((m+1) - 1) + 8) * max l r := by ring
      _ ≤ A * U.card := Nat.mul_le_mul hA hkU
  · have hcL : (preL S).card = (S ∩ Xs).card := by
      rw [← hpreL S hS, card_image_of_injective _ hψL]
    have hcR : (preR S).card = (S ∩ Ys).card := by
      rw [← hpreR S hS, card_image_of_injective _ hψR]
    have hbal' : (preL S).card = (preR S).card := by rw [hcL, hcR]; exact hbal
    simp only [dif_pos hbal']
    have := (hFm (preL S) (preR S) hbal').2.1
    rw [bal_portsB_image' hφL hφR, hpreL S hS, hpreR S hS] at this
    have hS' : S ∩ Xs ∪ S ∩ Ys = S := by
      rw [← inter_union_distrib_left]
      exact inter_eq_left.mpr (hS.trans hUXY)
    rwa [hS'] at this
  · intro y hy
    have hyU : y ∉ U := Finset.disjoint_left.mp hWU hy
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨x, -, rfl⟩ := mem_image.mp hy
      have hxK : Dt.φ x ∈ K := by
        rcases x with x | x
        · exact hXK ((hφS _).1 rfl)
        · exact hYK ((hφS _).2 rfl)
      exact (mem_union.mp (hKW hxK)).resolve_right hyU
    · exact hWin hy

  · have hPay : 0 ≤ ambientWeightedRoutePayment a m (L0+60) (Fintype.card Ambient) Wc.card := by
      have hp : 0 ≤ 200*ambientWeightedRoutePayment a m (L0+60) (Fintype.card Ambient) Wc.card :=
        weightedCoreRoutePay_nonneg a ha m _ _ L0
      linarith only [hp]
    have hCoeff : (QB.edgeFinset.card:ℝ) ≤ 200*(U.card:ℝ) := by
      exact_mod_cast hQBcard.trans (Nat.mul_le_mul_left 200 hkU)
    have hMult := mul_le_mul_of_nonneg_right hCoeff hPay
    change (count (R0∪mapConfiguration ι (Dt.pathEdges.image (selectorTriangle v))):ℝ) ≤ _
    dsimp only [weightedCoreRoutePay]
    nlinarith only [hCount,hMult]


end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.weighted_coreAvail_par

#print axioms TypedTriangle.Pasch.weighted_coreAvail_bal

#print axioms TypedTriangle.Pasch.weightedCoreRoutePay_nonneg
