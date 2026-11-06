/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V27.RoutedSelectors
public import RequestProject.Selectors.LocalContract

@[expose] public section

/-!
# V27 — single-component selector contract INSIDE the core (`CoreAvail`)

`CoreAvail G lab F v U Adm A ζw ρw Wc` is the single-root availability premise
`SelSimul.LocalAvail` with one extra conclusion: the non-port vertices `σ.W` of the selector
(auxiliary images AND route internals) lie in the core `Wc`.  The vertex window `Z0` it must
avoid contains NO root set: roots outside the core are avoided because `σ.W ⊆ Wc`.

`coreAvail_par` / `coreAvail_bal` produce it from a routing host `H ≤ L_v` (for every
forbidden edge window `Bf`) whose edges avoid `Bf` and whose vertices lie in `Wc ∪ U`, with the
robust odd path condition for `ParAllowed K` / `BalAllowed Xs Ys` (supplied by the V25 routes in
`coreHost`, `CoreComponent.lean`).  The selector is the existing V20 gadget routed by
`parity_selector_routed` / `balanced_selector_routed`.

Internal images avoid every port image: `portFree` (`σ.W ∩ U = ∅`) is part of the contract,
and `internal_host_adj` + `hHW` put each internal vertex in `Wc ∪ U`, hence in `Wc`.
-/

namespace S07V27

open Finset SimpleGraph SelBridge SelTyped SelSubdiv SelRoute ParitySel SelBalanced SelEmbed
open SelSimul

variable {V I : Type*} [DecidableEq V]

/-- **Availability premise of one root inside the core** (no root window). -/
def CoreAvail (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (U : Finset V) (Adm : Finset V → Prop) (A ζw ρw : ℕ) (Wc : Finset V) : Prop :=
  ∀ (Z0 : Finset V) (Bf : Finset (Sym2 V)), Z0.card ≤ ζw → (∀ y, edeg Bf y ≤ ρw) →
    ∃ σ : LocalSel V, σ.Valid G lab F v U Adm Z0 Bf A ∧ σ.W ⊆ Wc

/-- An empty port set is always available inside the core (empty selector). -/
theorem coreAvail_empty (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (Adm : Finset V → Prop) (A ζw ρw : ℕ) (Wc : Finset V) :
    CoreAvail G lab F v ∅ Adm A ζw ρw Wc :=
  fun Z0 Bf _ _ => ⟨_, valid_empty G lab F v Adm Z0 Bf A, by simp⟩

/-- An internal vertex of an odd subdivision is an end of a host edge. -/
lemma internal_host_adj {α : Type*} [DecidableEq α] {H : SimpleGraph V} {Q : Finset (Sym2 α)}
    (D : OddSubdivision H Q) {y : V} (hy : y ∈ D.internals) : ∃ z, H.Adj y z := by
  obtain ⟨e, he, j, h1, h2, rfl⟩ := (OddSubdivision.mem_internals _).mp hy
  have := D.adj e he j (by omega)
  have hj : pv D.φ D.src D.tgt D.t D.int e j = D.int e j := OddSubdivision.pathV_mid e h1 h2
  rw [hj] at this
  exact ⟨_, this⟩

lemma par_portset_image' {r : ℕ} {φ : PV r → V} {ψ : Fin r → V}
    (hφP : ∀ i, φ (pu i) = ψ i) (T : Finset (Fin r)) :
    (portSet T).image φ = T.image ψ := by
  ext y
  simp only [portSet, mem_image, mem_map, Function.Embedding.inl_apply]
  constructor
  · rintro ⟨x, ⟨i, hi, rfl⟩, rfl⟩; exact ⟨i, hi, (hφP i).symm⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨Sum.inl i, ⟨i, hi, rfl⟩, hφP i⟩

/-- **PAR instance of the core contract** (existing parity gadget, routed in a core host). -/
theorem coreAvail_par (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (U K Wc : Finset V) {A ζw ρw ℓ Bud : ℕ} (hA : 4 * (ℓ - 1) + 2 ≤ A)
    (hBud : ζw + 3 * U.card + (ℓ - 1) * (4 * U.card) ≤ Bud)
    (hUK : U ⊆ K) (hK : ζw + 3 * U.card ≤ K.card) (hKW : K ⊆ Wc ∪ U)
    (hKwing : ∀ a ∈ K, G.Adj v a)
    (hhost : ∀ Bf : Finset (Sym2 V), (∀ y, edeg Bf y ≤ ρw) →
      ∃ H : SimpleGraph V, H ≤ typedLink G lab F v ∧ (∀ x y, H.Adj x y → s(x, y) ∉ Bf) ∧
        (∀ x y, H.Adj x y → x ∈ Wc ∪ U) ∧ RobustOddPaths H (ParAllowed K) ℓ Bud) :
    CoreAvail G lab F v U (fun S => Even S.card) A ζw ρw Wc := by
  intro Z0 Bf hZ0 hBf
  obtain ⟨H, hHle, hHB, hHW, hR⟩ := hhost Bf hBf
  set r := U.card with hr
  let e := U.equivFin
  let ψ : Fin r → V := fun i => (e.symm i : V)
  have hψ : Function.Injective ψ := fun i j h => e.symm.injective (Subtype.ext h)
  have hψU : ∀ i, ψ i ∈ U := fun i => (e.symm i).2
  have hψsurj : ∀ u ∈ U, ∃ i, ψ i = u := fun u hu => ⟨e ⟨u, hu⟩, by simp [ψ]⟩
  have hZ0' : (Z0 \ U).card ≤ ζw := (card_le_card sdiff_subset).trans hZ0
  obtain ⟨Dt, hφP, hφC, hZ, hZi, -, -, -, hW, -, hdeg, hpe, hwing, hmodes⟩ :=
    parity_selector_routed G lab F v H hHle K (Z0 \ U) r ℓ Bud
      (by omega) hR hKwing ψ hψ (fun i => hUK (hψU i))
      (fun i h => (mem_sdiff.mp h).2 (hψU i)) (fun _ => K) (fun _ => subset_refl _)
      (fun _ => by show _ ≤ K.card; omega)
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
    if h : Even (pre S).card then Dt.modeEdges (Fm (pre S) h) else ∅⟩, ?_, ?_⟩
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
    obtain ⟨x, y, rfl, hH, -⟩ := hpe f hf
    exact hHB x y hH hfB
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
    calc 2 * r + (ℓ - 1) * (4 * r) = (4 * (ℓ - 1) + 2) * r := by ring
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
    · obtain ⟨z, hz⟩ := internal_host_adj Dt hy
      exact (mem_union.mp (hHW _ _ hz)).resolve_right hyU

/-- Balanced-selector port images. -/
lemma bal_portsB_image' {l r : ℕ} {φ : BV l r → V} {ψL : Fin l → V} {ψR : Fin r → V}
    (hL : ∀ p, φ (Sum.inl (Sum.inr p)) = ψL p) (hR : ∀ q, φ (Sum.inr (Sum.inr q)) = ψR q)
    (SL : Finset (Fin l)) (SR : Finset (Fin r)) :
    (OddSubdivision.portsB SL SR).image φ = SL.image ψL ∪ SR.image ψR := by
  ext y
  simp only [OddSubdivision.portsB, mem_image, mem_union]
  constructor
  · rintro ⟨x, (⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩), rfl⟩
    · exact Or.inl ⟨p, hp, (hL p).symm⟩
    · exact Or.inr ⟨q, hq, (hR q).symm⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact ⟨_, Or.inl ⟨p, hp, rfl⟩, hL p⟩
    · exact ⟨_, Or.inr ⟨q, hq, rfl⟩, hR q⟩

set_option maxHeartbeats 1000000 in
/-- **BAL instance of the core contract** (existing balanced gadget, routed in a core host;
nonempty port set). -/
theorem coreAvail_bal (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (U K Xs Ys Wc : Finset V) {A ζw ρw ℓ Bud : ℕ} (hU : U.Nonempty)
    (hA : 200 * (ℓ - 1) + 8 ≤ A)
    (hBud : ζw + 10 * U.card + (ℓ - 1) * (200 * U.card) ≤ Bud)
    (hXK : Xs ⊆ K) (hYK : Ys ⊆ K) (hXY : Disjoint Xs Ys) (hUXY : U ⊆ Xs ∪ Ys)
    (hXc : ζw + 10 * U.card ≤ Xs.card) (hYc : ζw + 10 * U.card ≤ Ys.card)
    (hKW : K ⊆ Wc ∪ U) (hKwing : ∀ a ∈ K, G.Adj v a)
    (hhost : ∀ Bf : Finset (Sym2 V), (∀ y, edeg Bf y ≤ ρw) →
      ∃ H : SimpleGraph V, H ≤ typedLink G lab F v ∧ (∀ x y, H.Adj x y → s(x, y) ∉ Bf) ∧
        (∀ x y, H.Adj x y → x ∈ Wc ∪ U) ∧ RobustOddPaths H (BalAllowed Xs Ys) ℓ Bud) :
    CoreAvail G lab F v U (fun S => (S ∩ Xs).card = (S ∩ Ys).card) A ζw ρw Wc := by
  intro Z0 Bf hZ0 hBf
  obtain ⟨H, hHle, hHB, hHW, hR⟩ := hhost Bf hBf
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
  have hMk : (Z0 \ U).card + 10 * max l r + (ℓ - 1) * (200 * max l r) ≤ Bud := by
    have : (ℓ - 1) * (200 * max l r) ≤ (ℓ - 1) * (200 * U.card) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨QB, -, -, -, Dt, hφL, hφR, -, hφS, hZ, hZi, -, -, -, hW, -, hdeg, hpe, hwing,
      hmodes⟩ :=
    balanced_selector_routed l r hk G lab F v H hHle K Xs Ys
      (Z0 \ U) ℓ Bud hMk hR hKwing hXK hYK hXY ψL ψR hψL hψR
      (fun p => (mem_inter.mp (hψLU p)).2) (fun q => (mem_inter.mp (hψRU q)).2)
      (fun p h => (mem_sdiff.mp h).2 (mem_inter.mp (hψLU p)).1)
      (fun q h => (mem_sdiff.mp h).2 (mem_inter.mp (hψRU q)).1)
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
    else ∅⟩, ?_, ?_⟩
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
    obtain ⟨x, y, rfl, hH, -⟩ := hpe f hf
    exact hHB x y hH hfB
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
    calc 8 * max l r + (ℓ - 1) * (200 * max l r) = (200 * (ℓ - 1) + 8) * max l r := by ring
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
    · obtain ⟨z, hz⟩ := internal_host_adj Dt hy
      exact (mem_union.mp (hHW _ _ hz)).resolve_right hyU

end S07V27
