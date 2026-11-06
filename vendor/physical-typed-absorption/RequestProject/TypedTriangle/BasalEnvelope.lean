/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SlotPairing
public import RequestProject.TypedTriangle.ElimPivots
public import RequestProject.Selectors.SimulCounters
@[expose] public section

/-! A bounded-load triangle envelope for paying a basal boundary.
The construction uses H3 and a finite saturation counter. It does not assume
that the boundary is physical or that a signed certificate is positive. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Envelope
open SelSimul
variable {V I : Type*} [Fintype V]

def wings (S : Finset (Sym2 V)) (ap : Sym2 V → V) : Finset (Sym2 V) :=
  S.biUnion (fun e => wedgeOf e (ap e))

def count (S : Finset (Sym2 V)) (ap : Sym2 V → V) (v : V) : ℕ :=
  auxCount S (fun e => {ap e}) v

lemma wedge_degree_le (e : Sym2 V) (a v : V) : edeg (wedgeOf e a) v ≤ 2 := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [wedgeOf_mk]
    exact (Finset.card_filter_le _ _).trans (by simpa only [wedge] using (Finset.card_le_two : ({s(x,a),s(y,a)} : Finset (Sym2 V)).card ≤ 2))

lemma wings_degree_le (E S : Finset (Sym2 V)) (ap : Sym2 V → V) {r q : ℕ}
    (hS : S ⊆ E) (hE : ∀ v, edeg E v ≤ r) (hc : ∀ v, count S ap v ≤ q) (v : V) :
    edeg (wings S ap) v ≤ 2 * (r + q) := by
  have hdeg := edeg_biUnion_le S (fun e => wedgeOf e (ap e))
    (fun e => e.toFinset ∪ {ap e}) (fun e he w => wedge_degree_le e (ap e) w)
    (fun e he f hf w hw => by
      obtain ⟨x, hx, rfl⟩ := mem_wedgeOf.mp hf
      rcases Sym2.mem_iff.mp hw with hw | hw
      · exact mem_union_left _ (Sym2.mem_toFinset.mpr (hw ▸ hx))
      · exact mem_union_right _ (by simpa using hw)) v
  have hcard := filter_or_card_le S (fun e => v ∈ e.toFinset) (fun e => v ∈ ({ap e} : Finset V))
  have hp : (S.filter (fun e => v ∈ e.toFinset)).card ≤ r := by
    simpa only [Sym2.mem_toFinset, edeg] using (edeg_mono hS v).trans (hE v)
  have ha : (S.filter (fun e => v ∈ ({ap e} : Finset V))).card ≤ q := hc v
  change edeg (wings S ap) v ≤ _ at hdeg
  simp only [mem_union] at hdeg
  exact hdeg.trans (Nat.mul_le_mul_left _ (by omega))

structure Assignment (H : Host V I) (F : Set (Multiset I))
    (E B : Finset (Sym2 V)) (Z : Finset V) (q : ℕ)
    (S : Finset (Sym2 V)) (ap : Sym2 V → V) : Prop where
  tri : ∀ e ∈ S, IsAllowed H F (slotTri e (ap e))
  avoid : ∀ e ∈ S, ap e ∉ Z
  fresh : ∀ e ∈ S, Disjoint (wedgeOf e (ap e)) (E ∪ B)
  disj : (S : Set (Sym2 V)).PairwiseDisjoint (fun e => wedgeOf e (ap e))
  cnt : ∀ v, count S ap v ≤ q

/-- The envelope assignment is constructed greedily with bounded centre load.
The window pays the whole base universe, protected edges, used wings and saturation. -/
theorem assignment_of_H3 {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) (E B : Finset (Sym2 V)) (Z : Finset V)
    {r b q : ℕ} (hq : 0 < q) (hE : ∀ v, edeg E v ≤ r) (hB : ∀ v, edeg B v ≤ b)
    (htri : ∀ e ∈ E, HasTri H F e)
    (hwin : ((Z.card + E.card / q + 2 * (b + 3 * r + 2 * q) : ℕ) : ℝ) <
      α * Fintype.card V) :
    ∃ ap : Sym2 V → V, Assignment H F E B Z q E ap := by
  classical
  have key : ∀ S : Finset (Sym2 V), S ⊆ E →
      ∃ ap : Sym2 V → V, Assignment H F E B Z q S ap := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun e => (Quot.out e).1, ?_⟩
      exact ⟨by simp, by simp, by simp, by simp, by simp [count, auxCount]⟩
    | insert e S he ih =>
      intro hsub
      have heE := hsub (mem_insert_self e S)
      have hSE : S ⊆ E := (subset_insert e S).trans hsub
      obtain ⟨ap, h⟩ := ih hSE
      let Sat := satSet S (fun f => ({ap f} : Finset V)) q
      have hSat : Sat.card ≤ E.card / q := by
        have hs := satSet_card_le S (fun f => ({ap f} : Finset V)) hq
          (a := 1) (by simp)
        simpa using hs.trans (Nat.div_le_div_right (by simpa using card_le_card hSE))
      let Bad := (B ∪ E) ∪ wings S ap
      have hd : ∀ v, degIn Bad v ≤ b + 3 * r + 2 * q := by
        intro v
        have h1 := edeg_union_le (B ∪ E) (wings S ap) v
        have h2 := edeg_union_le B E v
        have h3 := wings_degree_le E S ap hSE hE h.cnt v
        have h4 := hE v
        have h5 := hB v
        change edeg Bad v ≤ _
        dsimp [Bad]
        omega
      obtain ⟨u,v,a,heuv,hTa⟩ := htri e heE |>.exists_tri
      let X := ((Z ∪ Sat) ∪ nbrIn Bad u) ∪ nbrIn Bad v
      have hXc : X.card ≤ Z.card + E.card / q + 2 * (b + 3 * r + 2 * q) := by
        have h1 := card_union_le (Z ∪ Sat) (nbrIn Bad u)
        have h2 := card_union_le Z Sat
        have h3 := card_union_le ((Z ∪ Sat) ∪ nbrIn Bad u) (nbrIn Bad v)
        have h4 := (card_nbrIn_le Bad u).trans (hd u)
        have h5 := (card_nbrIn_le Bad v).trans (hd v)
        dsimp [X]
        omega
      have hX : (X.card : ℝ) < α * Fintype.card V := by
        have hc : (X.card : ℝ) ≤ (Z.card + E.card / q + 2 * (b + 3 * r + 2 * q) : ℕ) := by
          exact_mod_cast hXc
        exact hc.trans_lt hwin
      obtain ⟨w,hTw,hwX⟩ := exists_fresh_apex hH3 hTa X hX
      have hwZ : w ∉ Z := fun hw => hwX (by simp [X,hw])
      have hwSat : w ∉ Sat := fun hw => hwX (by simp [X,hw])
      have hwu : s(u,w) ∉ Bad := fun hf => hwX (by simp [X,nbrIn,hf])
      have hwv : s(v,w) ∉ Bad := fun hf => hwX (by simp [X,nbrIn,hf])
      have hnew : Disjoint (wedgeOf e w) Bad := by
        rw [heuv,wedgeOf_mk]
        exact Finset.disjoint_left.mpr (by
          intro f hf hfb
          rcases (show f = s(u,w) ∨ f = s(v,w) by simpa [wedge] using hf) with rfl | rfl
          · exact hwu hfb
          · exact hwv hfb)
      let ap' := Function.update ap e w
      have hupd : ∀ f ∈ S, ap' f = ap f := by
        intro f hf
        exact Function.update_of_ne (by rintro rfl; exact he hf) _ _
      have hc : ∀ x, count (insert e S) ap' x ≤ q := by
        intro x
        apply auxCount_insert_le he (fun f => ({ap' f} : Finset V)) hq
        · intro y
          rw [auxCount_congr (fun f hf => by rw [hupd f hf])]
          exact h.cnt y
        · rw [satSet_congr (fun f hf => by rw [hupd f hf])]
          simp only [ap', Function.update_self]
          exact disjoint_singleton_left.mpr hwSat
      refine ⟨ap', ?_⟩
      refine ⟨?_, ?_, ?_, ?_, hc⟩
      · intro f hf
        rcases mem_insert.mp hf with rfl | hf
        · simpa [ap',heuv,slotTri_mk] using hTw
        · rw [hupd f hf]; exact h.tri f hf
      · intro f hf
        rcases mem_insert.mp hf with rfl | hf
        · simpa [ap'] using hwZ
        · rw [hupd f hf]; exact h.avoid f hf
      · intro f hf
        rcases mem_insert.mp hf with rfl | hf
        · simp only [ap',Function.update_self]
          exact hnew.mono_right (by intro f hf; exact mem_union_left _ (by
            rcases mem_union.mp hf with hf | hf
            · exact mem_union_right _ hf
            · exact mem_union_left _ hf))
        · rw [hupd f hf]; exact h.fresh f hf
      · intro f hf f' hf' hne
        change Disjoint (wedgeOf f (ap' f)) (wedgeOf f' (ap' f'))
        have hP : ∀ f ∈ S, Disjoint (wedgeOf e w) (wedgeOf f (ap f)) := by
          intro f hf
          exact hnew.mono_right (fun g hg => mem_union_right _ (mem_biUnion.mpr ⟨f,hf,hg⟩))
        rcases mem_insert.mp hf with hfe | hfS <;> rcases mem_insert.mp hf' with hfe' | hfS'
        · exact absurd (hfe.trans hfe'.symm) hne
        · rw [hfe,show ap' e = w by simp [ap'],hupd f' hfS']; exact hP f' hfS'
        · rw [hfe',show ap' e = w by simp [ap'],hupd f hfS]; exact (hP f hfS).symm
        · rw [hupd f hfS,hupd f' hfS']; exact h.disj hfS hfS' hne
  exact key E subset_rfl

lemma Assignment.base_distinct {H : Host V I} {F : Set (Multiset I)}
    {E B S : Finset (Sym2 V)} {Z : Finset V} {q : ℕ} {ap : Sym2 V → V}
    (h : Assignment H F E B Z q S ap) {e : Sym2 V} (he : e ∈ S) :
    ¬ e.IsDiag ∧ ap e ∉ e := by
  induction e using Sym2.ind with
  | _ u v =>
    have ht : IsAllowed H F {u,v,ap s(u,v)} := by
      simpa only [slotTri_mk] using h.tri s(u,v) he
    obtain ⟨huv,hua,hva⟩ := distinct_of_card_three ht.1
    exact ⟨by simpa, by simp [hua.symm,hva.symm]⟩

lemma Assignment.envelope_basal {H : Host V I} {F : Set (Multiset I)}
    {E B : Finset (Sym2 V)} {Z : Finset V} {q : ℕ} {ap : Sym2 V → V}
    (h : Assignment H F E B Z q E ap) : Basal H F (E ∪ wings E ap) := by
  have hdisj : (E : Set (Sym2 V)).PairwiseDisjoint
      (fun e => triEdges (slotTri e (ap e))) := by
    intro e he f hf hne
    obtain ⟨heD,heA⟩ := h.base_distinct he
    obtain ⟨hfD,hfA⟩ := h.base_distinct hf
    change Disjoint (triEdges (slotTri e (ap e))) (triEdges (slotTri f (ap f)))
    rw [triEdges_slotTri heD heA,triEdges_slotTri hfD hfA]
    apply disjoint_left.mpr
    intro g hg hg'
    rcases mem_insert.mp hg with hge | hgw <;> rcases mem_insert.mp hg' with hgf | hgw'
    · exact hne (hge.symm.trans hgf)
    · exact disjoint_left.mp (h.fresh f hf) hgw' (mem_union_left _ (hge ▸ he))
    · exact disjoint_left.mp (h.fresh e he) hgw (mem_union_left _ (hgf ▸ hf))
    · exact disjoint_left.mp (h.disj he hf hne) hgw hgw'
  have hbas := basal_biUnion E (fun e => triEdges (slotTri e (ap e)))
    (fun e he => basal_triEdges (h.tri e he)) hdisj
  apply hbas.congr
  ext g
  simp only [mem_biUnion,mem_union,wings]
  constructor
  · rintro ⟨e,he,hg⟩
    obtain ⟨heD,heA⟩ := h.base_distinct he
    rw [triEdges_slotTri heD heA] at hg
    rcases mem_insert.mp hg with hge | hg
    · exact Or.inl (hge ▸ he)
    · exact Or.inr ⟨e,he,hg⟩
  · rintro (hg | hg)
    · obtain ⟨hgD,hgA⟩ := h.base_distinct hg
      exact ⟨g,hg,by rw [triEdges_slotTri hgD hgA]; simp⟩
    · obtain ⟨e,he,hge⟩ := hg
      obtain ⟨heD,heA⟩ := h.base_distinct he
      exact ⟨e,he,by rw [triEdges_slotTri heD heA]; exact mem_insert_of_mem hge⟩

/-- A genuine triangle-decomposable envelope is constructed from H3.
The boundary E need not be divisible or physical. The new wings avoid all bases
and protected edges, and have maximum degree at most 2(r+q). -/
theorem envelope_of_H3 {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) (E B : Finset (Sym2 V)) (Z : Finset V)
    {r b q : ℕ} (hq : 0 < q) (hE : ∀ v, edeg E v ≤ r) (hB : ∀ v, edeg B v ≤ b)
    (htri : ∀ e ∈ E, HasTri H F e)
    (hwin : ((Z.card + E.card / q + 2 * (b + 3 * r + 2 * q) : ℕ) : ℝ) <
      α * Fintype.card V) :
    ∃ W : Finset (Sym2 V), Disjoint W (E ∪ B) ∧ Basal H F (E ∪ W) ∧
      ∀ v, edeg W v ≤ 2 * (r + q) := by
  obtain ⟨ap,h⟩ := assignment_of_H3 hH3 E B Z hq hE hB htri hwin
  refine ⟨wings E ap, ?_, h.envelope_basal, wings_degree_le E E ap subset_rfl hE h.cnt⟩
  rw [wings,disjoint_biUnion_left]
  exact h.fresh

/-- Paying the empty residual makes the enlarged fuel basal. -/
lemma pay_empty_mode {H : Host V I} {F : Set (Multiset I)}
    {R K W : Finset (Sym2 V)} (hK : K ⊆ R) (hR : Basal H F (R \ K))
    (hKW : Basal H F (K ∪ W)) (hWR : Disjoint W R) : Basal H F (R ∪ W) := by
  have hd : Disjoint (R \ K) (K ∪ W) := by
    apply disjoint_left.mpr
    intro e he he'
    rcases mem_union.mp he' with heK | heW
    · exact (mem_sdiff.mp he).2 heK
    · exact disjoint_left.mp hWR heW (mem_sdiff.mp he).1
  apply (hR.union hKW hd).congr
  ext e
  simp only [mem_union,mem_sdiff]
  constructor
  · tauto
  · rintro (he | heW)
    · by_cases heK : e ∈ K <;> tauto
    · tauto

/-- Constructive basal payment, with all protected edges kept untouched.
The empty-mode partition supplies R\K; H3 constructs the missing payment for K. -/
theorem basal_payment_of_H3 {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) (R K X B : Finset (Sym2 V))
    {r b q : ℕ} (hq : 0 < q) (hK : K ⊆ R) (hR : Basal H F (R \ K))
    (hKd : ∀ v, edeg K v ≤ r) (hprot : ∀ v, edeg (R ∪ X ∪ B) v ≤ b)
    (htri : ∀ e ∈ K, HasTri H F e)
    (hwin : ((K.card / q + 2 * (b + 3 * r + 2 * q) : ℕ) : ℝ) <
      α * Fintype.card V) :
    ∃ W : Finset (Sym2 V), Disjoint W (R ∪ X ∪ B) ∧
      Basal H F (R ∪ W) ∧ Basal H F (K ∪ W) ∧ ∀ v, edeg W v ≤ 2 * (r + q) := by
  obtain ⟨W,hW,hKW,hd⟩ := envelope_of_H3 hH3 K (R ∪ X ∪ B) ∅ hq hKd hprot htri
    (by simpa only [card_empty,zero_add] using hwin)
  have hWP : Disjoint W (R ∪ X ∪ B) := hW.mono_right subset_union_right
  have hWR : Disjoint W R := hWP.mono_right (fun e he => mem_union_left _ (mem_union_left _ he))
  exact ⟨W,hWP,pay_empty_mode hK hR hKW hWR,hKW,hd⟩

/-- Original H2 supplies the structural third-triangle premise on every host edge. -/
lemma hasTri_of_physical_host {H : Host V I} {F : Set (Multiset I)}
    (hH2 : IsPhysical H F (edges H)) {e : Sym2 V} (he : e ∈ edges H) :
    HasTri H F e := by
  apply hasTri_of_ne (lattice_le_localGroup H F hH2)
  simp [ind,he]

/-- The original H2--H3 suffice for an envelope of any sparse host-edge set.
Only the displayed construction-resource window is required in addition. -/
theorem envelope_of_H2H3 {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH2 : IsPhysical H F (edges H)) (hH3 : CommonNbrCond H F α)
    (E B : Finset (Sym2 V)) (Z : Finset V) (hEH : E ⊆ edges H)
    {r b q : ℕ} (hq : 0 < q) (hE : ∀ v, edeg E v ≤ r) (hB : ∀ v, edeg B v ≤ b)
    (hwin : ((Z.card + E.card / q + 2 * (b + 3 * r + 2 * q) : ℕ) : ℝ) <
      α * Fintype.card V) :
    ∃ W : Finset (Sym2 V), Disjoint W (E ∪ B) ∧ Basal H F (E ∪ W) ∧
      ∀ v, edeg W v ≤ 2 * (r + q) :=
  envelope_of_H3 hH3 E B Z hq hE hB
    (fun e he => hasTri_of_physical_host hH2 (hEH he)) hwin

end TypedTriangle.Envelope
