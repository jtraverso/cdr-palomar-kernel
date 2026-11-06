/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ImageTransfer
public import RequestProject.S07V27.CoreComponent
public import RequestProject.S07V45.CoreLink
public import RequestProject.S07V45.CoreContract
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Transporting the already formalized odd route property into induced
links, with no assumption that the root of the link lies in the sample. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.RawReference

private def walk_inducedOn {V : Type*} {J : SimpleGraph V}
    {W : Finset V} {a b : V} (p : J.Walk a b)
    (hp : ∀ u ∈ p.support, u ∈ W) :
    (Incidence.inducedOn J W).Walk a b := by
  induction p with
  | nil => exact SimpleGraph.Walk.nil
  | @cons a c b hac p ih =>
    have ha : a ∈ W := hp a (by simp)
    have hc : c ∈ W := hp c (by simp)
    exact SimpleGraph.Walk.cons ⟨hac,ha,hc⟩
      (ih (fun u hu => hp u (by simp [hu])))

private lemma walk_inducedOn_length {V : Type*} {J : SimpleGraph V}
    {W : Finset V} {a b : V} (p : J.Walk a b)
    (hp : ∀ u ∈ p.support, u ∈ W) :
    (walk_inducedOn p hp).length = p.length := by
  induction p with
  | nil => rfl
  | @cons a c b hac p ih =>
    simp only [walk_inducedOn, SimpleGraph.Walk.length_cons]
    exact congrArg (fun n => n + 1) (ih (fun u hu => hp u (by simp [hu])))

theorem route_admissible_walk {V I : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {t : ℕ} {ε : ℝ} {W : Finset V}
    (hε : 0 < ε) (hroute : S07V27.RouteProp G lab F t ε W)
    {v a b : V} (ha : a ∈ W) (hb : b ∈ W)
    (hadm : S07V24.AdmPair (S07V25.activeComps G lab F)
      (fun v C => TypedTriangle.ComponentRows.IsBip G lab F (v,C))
      (S07V25.colG G lab F) v a b) :
    ∃ p : (Incidence.inducedOn (TypedTriangle.ComponentRows.link G lab F v) W).Walk a b,
      p.length = t := by
  obtain ⟨p,hp,hW,-,-⟩ := hroute ∅ ⊥ 0 (by simp; positivity)
    (fun _ => by simp) (by simp; positivity) v a b hadm
  have hlen := S07V27.pathsLen_length hp
  have hs : ∀ u ∈ p.support, u ∈ W := by
    intro u hu
    obtain ⟨k,rfl,hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hu
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [SimpleGraph.Walk.getVert_zero]
      exact ha
    · rcases lt_or_eq_of_le hk with hlt | heq
      · exact hW ((S07V24.mem_intlSet _ _ _).2 ⟨⟨k-1,by omega⟩,by
          simp [S07V24.intl]; congr 1; omega⟩)
      · rw [heq,SimpleGraph.Walk.getVert_length]
        exact hb
  exact ⟨walk_inducedOn p hs, (walk_inducedOn_length p hs).trans hlen⟩

theorem route_admissible_reachable {V I : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {t : ℕ} {ε : ℝ} {W : Finset V}
    (hε : 0 < ε) (hroute : S07V27.RouteProp G lab F t ε W)
    {v a b : V} (ha : a ∈ W) (hb : b ∈ W)
    (hadm : S07V24.AdmPair (S07V25.activeComps G lab F)
      (fun v C => TypedTriangle.ComponentRows.IsBip G lab F (v,C))
      (S07V25.colG G lab F) v a b) :
    (Incidence.inducedOn (TypedTriangle.ComponentRows.link G lab F v) W).Reachable a b := by
  obtain ⟨p,-⟩ := route_admissible_walk hε hroute ha hb hadm
  exact ⟨p⟩

/-- Routes of admissible pairs also connect same-side bipartite pairs: the first
internal vertex of a route starting at `a` supplies an opposite-side pivot. -/
theorem route_component_reachable {V I : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {t : ℕ} {ε : ℝ} {W : Finset V}
    (ht3 : 3 ≤ t) (hε : 0 < ε)
    (hroute : S07V27.RouteProp G lab F t ε W)
    {v : V} {C : Finset V} (hC : C ∈ S07V25.activeComps G lab F v)
    {a b : V} (haC : a ∈ C) (hbC : b ∈ C)
    (haW : a ∈ W) (hbW : b ∈ W) :
    (Incidence.inducedOn (TypedTriangle.ComponentRows.link G lab F v) W).Reachable a b := by
  by_cases hab : a = b
  · subst hab
    exact SimpleGraph.Reachable.refl _
  by_cases hB : TypedTriangle.ComponentRows.IsBip G lab F (v,C)
  · by_cases hcol : S07V25.colG G lab F v a = S07V25.colG G lab F v b
    · obtain ⟨x, ⟨y, hxy⟩, hCx⟩ := S07V25.mem_activeComps.mp hC
      have hnbr : ∃ y, (TypedTriangle.ComponentRows.link G lab F v).Adj a y := by
        have haComp : a ∈ TypedTriangle.ComponentRows.comp G lab F v x := hCx ▸ haC
        rw [S07V25.mem_comp_iff] at haComp
        obtain ⟨p⟩ := haComp.symm
        cases p with
        | nil => exact ⟨y, hxy⟩
        | cons h _ => exact ⟨_, h⟩
      obtain ⟨y, hay⟩ := hnbr
      have hyC := S07V27.activeComp_closed hC haC hay
      have hayAdm := S07V27.activeComp_admPair hC haC hyC hay.ne
        (fun h => S07V27.activeComp_colG_ne hC h haC hyC hay)
      have h0 : (0:ℝ) ≤ ε * Fintype.card V := by positivity
      obtain ⟨z,hzW,_,haz⟩ := S07V27.route_first_internal ht3 hε hroute
        ∅ (by simpa using h0) hayAdm
      have hzC := S07V27.activeComp_closed hC haC haz
      have hcolaz := S07V27.activeComp_colG_ne hC hB haC hzC haz
      have hcolbz : S07V25.colG G lab F v b ≠ S07V25.colG G lab F v z := by
        simpa [← hcol] using hcolaz
      have hbz : b ≠ z := by
        intro h
        exact hcolbz (by rw [h])
      have hAdm : S07V24.AdmPair (S07V25.activeComps G lab F)
          (fun v C => TypedTriangle.ComponentRows.IsBip G lab F (v,C))
          (S07V25.colG G lab F) v b z :=
        S07V27.activeComp_admPair hC hbC hzC hbz (fun _ => hcolbz)
      have haz' : (Incidence.inducedOn
          (TypedTriangle.ComponentRows.link G lab F v) W).Adj a z := ⟨haz,haW,hzW⟩
      exact haz'.reachable.trans
        (route_admissible_reachable hε hroute hbW hzW hAdm).symm
    · exact route_admissible_reachable hε hroute haW hbW
        (S07V27.activeComp_admPair hC haC hbC hab (fun _ => hcol))
  · exact route_admissible_reachable hε hroute haW hbW
      (S07V27.activeComp_admPair hC haC hbC hab (fun h => False.elim (hB h)))

#print axioms route_component_reachable

/-- Root-link connectivity is retained by any robust route sample, even if
the root itself is not sampled. -/
theorem route_reachable_all {V I : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {t : ℕ} {ε : ℝ} {W : Finset V}
    (ht3 : 3 ≤ t) (hε : 0 < ε)
    (hroute : S07V27.RouteProp G lab F t ε W)
    (v : V) {a b : V} (haW : a ∈ W) (hbW : b ∈ W)
    (hab : (TypedTriangle.ComponentRows.link G lab F v).Reachable a b) :
    (Incidence.inducedOn (TypedTriangle.ComponentRows.link G lab F v) W).Reachable a b := by
  obtain ⟨p⟩ := hab
  cases p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a c b hac p =>
    have hC := S07V27.mem_activeComps_of_link hac
    have hbC : b ∈ TypedTriangle.ComponentRows.comp G lab F v a := by
      rw [S07V25.mem_comp_iff]
      exact hac.reachable.trans ⟨p⟩
    exact route_component_reachable ht3 hε hroute hC.1 hC.2 hbC haW hbW

#print axioms route_reachable_all

private theorem three_mem_of_card {V : Type*} [DecidableEq V]
    {S : Finset V} (hS : 3 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ b ≠ c ∧ c ≠ a := by
  have hpos : 0 < S.card := by omega
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hpos
  have hpos1 : 0 < (S.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b,hb⟩ := Finset.card_pos.mp hpos1
  have hb0 := Finset.mem_erase.mp hb
  have hpos2 : 0 < ((S.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
    omega
  obtain ⟨c,hc⟩ := Finset.card_pos.mp hpos2
  have hc0 := Finset.mem_erase.mp hc
  have hc1 := Finset.mem_erase.mp hc0.2
  exact ⟨a,ha,b,hb0.2,c,hc1.2,hb0.1.symm,hc0.1.symm,hc1.1⟩

/-- A nonbipartite active link component retains an odd closed walk in the
same Bernoulli core that carries the robust routes. -/
theorem route_nonbip_oddAt {V I : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {t : ℕ} {ε : ℝ} {W : Finset V}
    (ht3 : 3 ≤ t) (htodd : Odd t) (hε : 0 < ε)
    (hlarge : 2 ≤ ⌊ε * Fintype.card V⌋₊)
    (hroute : S07V27.RouteProp G lab F t ε W)
    {v : V} {C : Finset V} (hC : C ∈ S07V25.activeComps G lab F v)
    (hnb : ¬ TypedTriangle.ComponentRows.IsBip G lab F (v,C))
    {a : V} (haC : a ∈ C) (haW : a ∈ W) :
    Incidence.OddAt (Incidence.inducedOn
      (TypedTriangle.ComponentRows.link G lab F v) W) a := by
  have hpool := S07V27.route_pool_large ht3 hε hroute hC
  obtain ⟨x,hx,y,hy,z,hz,hxy,hyz,hzx⟩ :=
    three_mem_of_card (S := C ∩ W) (by omega)
  have hxC := (Finset.mem_inter.mp hx).1
  have hyC := (Finset.mem_inter.mp hy).1
  have hzC := (Finset.mem_inter.mp hz).1
  have hxW := (Finset.mem_inter.mp hx).2
  have hyW := (Finset.mem_inter.mp hy).2
  have hzW := (Finset.mem_inter.mp hz).2
  have hadmXY := S07V27.activeComp_admPair hC hxC hyC hxy (fun hb => False.elim (hnb hb))
  have hadmYZ := S07V27.activeComp_admPair hC hyC hzC hyz (fun hb => False.elim (hnb hb))
  have hadmZX := S07V27.activeComp_admPair hC hzC hxC hzx (fun hb => False.elim (hnb hb))
  obtain ⟨pXY,hpXY⟩ := route_admissible_walk hε hroute hxW hyW hadmXY
  obtain ⟨pYZ,hpYZ⟩ := route_admissible_walk hε hroute hyW hzW hadmYZ
  obtain ⟨pZX,hpZX⟩ := route_admissible_walk hε hroute hzW hxW hadmZX
  have hoddx : Incidence.OddAt (Incidence.inducedOn
      (TypedTriangle.ComponentRows.link G lab F v) W) x := by
    refine ⟨(pXY.append pYZ).append pZX, ?_⟩
    have hodd3 : Odd (t + t + t) := by
      rcases htodd with ⟨k,hk⟩
      refine ⟨3*k+1, ?_⟩
      omega
    simpa [hpXY,hpYZ,hpZX] using hodd3
  have hax := route_component_reachable ht3 hε hroute hC haC hxC haW hxW
  exact Incidence.oddAt_of_reach hax hoddx

#print axioms route_nonbip_oddAt

/-- Original oddness forces the original active component to be nonbipartite;
the sampled robust routes then transport oddness for every root. -/
theorem route_oddAt_all {V I : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {t : ℕ} {ε : ℝ} {W : Finset V}
    (ht3 : 3 ≤ t) (htodd : Odd t) (hε : 0 < ε)
    (hlarge : 2 ≤ ⌊ε * Fintype.card V⌋₊)
    (hroute : S07V27.RouteProp G lab F t ε W)
    (v : V) {a : V} (haW : a ∈ W)
    (hodd : Incidence.OddAt (TypedTriangle.ComponentRows.link G lab F v) a) :
    Incidence.OddAt (Incidence.inducedOn
      (TypedTriangle.ComponentRows.link G lab F v) W) a := by
  obtain ⟨p,hp⟩ := hodd
  cases p with
  | nil => simp at hp
  | cons hac p =>
    have hC := S07V27.mem_activeComps_of_link hac
    have hnb : ¬ TypedTriangle.ComponentRows.IsBip G lab F
        (v, TypedTriangle.ComponentRows.comp G lab F v a) := by
      intro hB
      have hproper : ∀ u ∈ TypedTriangle.ComponentRows.comp G lab F v a,
          ∀ w ∈ TypedTriangle.ComponentRows.comp G lab F v a,
          (TypedTriangle.ComponentRows.link G lab F v).Adj u w →
          TypedTriangle.ComponentRows.col G lab F
            (v,TypedTriangle.ComponentRows.comp G lab F v a) u ≠
          TypedTriangle.ComponentRows.col G lab F
            (v,TypedTriangle.ComponentRows.comp G lab F v a) w := by
        intro u hu w hw huw
        exact S07V45.col_proper hB hu hw huw
      have hs : ∀ u ∈ (SimpleGraph.Walk.cons hac p).support,
          u ∈ TypedTriangle.ComponentRows.comp G lab F v a := by
        intro u hu
        rw [S07V25.mem_comp_iff]
        exact S07V45.support_reach (SimpleGraph.Walk.cons hac p) u hu
      have hpar := S07V45.walk_col_parity G lab F hproper
        (SimpleGraph.Walk.cons hac p) hs
      have hlen : Odd (p.length + 1) := by
        simpa only [SimpleGraph.Walk.length_cons] using hp
      simp [hlen] at hpar
    exact route_nonbip_oddAt ht3 htodd hε hlarge hroute hC.1 hnb hC.2 haW

#print axioms route_oddAt_all

/-- The V25/S07 robust route sample is a G1-Z good-root sample for all
roots, including those omitted from the sample. -/
theorem route_goodRoot {V I : Type*} [Fintype V] [DecidableEq V]
    (H : Host V I) (F : Set (Multiset I)) {t : ℕ} {ε : ℝ}
    {W : Finset V} (ht3 : 3 ≤ t) (htodd : Odd t) (hε : 0 < ε)
    (hlarge : 2 ≤ ⌊ε * Fintype.card V⌋₊)
    (hroute : S07V27.RouteProp H.G H.lab F t ε W)
    (v : V) : GoodRoot H F W v := by
  constructor
  · intro a ha b hb hab
    change (Incidence.inducedOn
      (TypedTriangle.ComponentRows.link H.G H.lab F v) W).Reachable a b
    exact route_reachable_all ht3 hε hroute v ha hb hab
  · intro a ha hodd
    change Incidence.OddAt (Incidence.inducedOn
      (TypedTriangle.ComponentRows.link H.G H.lab F v) W) a
    exact route_oddAt_all ht3 htodd hε hlarge hroute v ha hodd

#print axioms route_goodRoot

#print axioms route_admissible_reachable

end TypedTriangle.RawReference
