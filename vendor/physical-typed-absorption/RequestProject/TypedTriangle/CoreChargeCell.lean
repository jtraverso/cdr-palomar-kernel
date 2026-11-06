/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.BoundedChargeCell
public import RequestProject.TypedTriangle.CoreBasalPayment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.ChargePolar
open CorePayment
variable {V I : Type*} [Fintype V]

lemma zeroExtend_ind_liftEdges (Z : Finset V) (Y : Finset (Sym2 (Survivors Z))) :
    edgeZeroExtend Z (ind Y) = ind (liftEdges Z Y) := by
  funext e
  by_cases he : ∀ v ∈ e, v ∉ Z
  · have hback := Sym2.attachWith_map_subtypeVal he
    rw [←hback,edgeZeroExtend_apply_map]
    simp only [ind,liftEdges,mem_image]
    congr 1
    apply propext
    exact ⟨fun hy => ⟨_,hy,rfl⟩,fun ⟨f,hf,hfe⟩ =>
      (edgeLift_injective Z hfe) ▸ hf⟩
  · have ht : TouchZ Z e := by
      push_neg at he
      obtain ⟨v,hve,hv⟩ := he
      exact ⟨v,hv,hve⟩
    rw [edgeZeroExtend_vanish Z _ e ht]
    apply Eq.symm
    apply if_neg
    intro hy
    obtain ⟨v,hv,hve⟩ := ht
    exact (liftEdges_avoids Z Y e hy v hve) hv

/-- A physical two-mode cell with its charge and positive payload on the genuine
core subtype, while its absorber lies in the ambient host. -/
theorem core_integer_charge_cell (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ K n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I)
      (F : Set (Multiset I)) (Z : Finset V) (β : ℝ),
      n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
      CommonNbrCond (restrictedHost H Z) F β →
      ∀ (x : Sym2 (Survivors Z) → ℤ) (U : Finset (Survivors Z)) (k : ℕ),
      (∑ e, |x e|) ≤ (k:ℤ) →
      x ∈ Composition.localProfile (restrictedHost H Z).G (restrictedHost H Z).lab F →
      (∀ e, x e ≠ 0 → ∀ v ∈ e, v ∈ U) → edgeZeroExtend Z x ∈ lattice H F →
      ∀ (B : Finset (Sym2 V)) (b Ub : ℕ), (∀ v, SelSimul.edeg B v ≤ b) →
      ((U.card+3*k+2*b+2:ℕ):ℝ) < β*Fintype.card (Survivors Z) →
      U.card+3*k+3*(K*(4*k))+K*(4*k)*(2*h-2)+3*(K*(4*k))*(2*h-3) ≤ Ub →
      (Ub:ℝ)+3+4*b < α*Fintype.card V →
      ((Ub:ℝ)+1+h+5*b)*2^(Nat.choose h 2) ≤ α/2*Fintype.card V →
      ∃ (A : Finset (Sym2 V)) (Y : Finset (Sym2 (Survivors Z))),
        Y.card ≤ 4*k ∧ Y ⊆ edges (restrictedHost H Z) ∧
        Disjoint (liftEdges Z Y) B ∧ Disjoint A B ∧ Disjoint A (liftEdges Z Y) ∧
        Basal H F (A∪liftEdges Z Y) ∧ Basal H F A ∧
        (A∪liftEdges Z Y).card ≤ K*(4*k)*(4*(2*h-2).choose 2+6)+4*k ∧
        ind Y-x ∈ lattice (restrictedHost H Z) F := by
  obtain ⟨K,n₀,hG2⟩ := slot_absorber_of_H3H4 α h hα
  refine ⟨K,n₀,?_⟩
  intro V I _ H F Z β hn h3 h4 hJ3 x U k hnorm hx hroots hxG B b Ub hB hw hUb hw1 hw2
  letI : DecidableEq (Survivors Z) := Classical.decEq _
  have hPull : ∀ v, SelSimul.edeg (pullEdges Z B) v ≤ b := by
    intro v
    simpa only [edeg_eq_classical] using (degree_pull_le Z B v).trans (hB v.1)
  obtain ⟨Aux,Y,hAux,hAuxU,hY,hYB,hFresh,hInside,hEdges,hRel⟩ :=
    integer_polarization hJ3 x U k hnorm (local_profile_hasTri (restrictedHost H Z) F x hx)
      hroots (pullEdges Z B) hPull hw
  have hYLB : Disjoint (liftEdges Z Y) B := by
    apply disjoint_left.mpr
    intro e he heB
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact disjoint_left.mp hYB hf (mem_preimage.mpr heB)
  have hPhys : IsPhysical H F (liftEdges Z Y) := by
    have hh := edgeZeroExtend_mem_lattice H F Z hRel
    have hhG := lattice_mono (vertexDeleted_le H Z) rfl hh
    rw [map_sub,zeroExtend_ind_liftEdges] at hhG
    have hsum := (lattice H F).add_mem hhG hxG
    change ind (liftEdges Z Y) ∈ lattice H F
    simpa only [sub_add_cancel] using hsum
  have hInsideL : Inside (liftVertexSet Z (U∪Aux)) (liftEdges Z Y) := by
    intro e he v hv
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
    exact mem_map.mpr ⟨w,hInside f hf w hw,rfl⟩
  have hYcard : (liftEdges Z Y).card ≤ 4*k :=
    card_image_le.trans hY
  have hRoot : (liftVertexSet Z (U∪Aux)).card ≤ U.card+3*k := by
    rw [card_liftVertexSet]
    exact (card_union_le _ _).trans (Nat.add_le_add_left hAux _)
  have hBudget : (liftVertexSet Z (U∪Aux)).card+3*(K*(liftEdges Z Y).card)+
      K*(liftEdges Z Y).card*(2*h-2)+3*(K*(liftEdges Z Y).card)*(2*h-3) ≤ Ub := by
    apply le_trans _ hUb
    gcongr
  obtain ⟨A,hAbs,hAB,hAc⟩ := hG2 H F hn h3 h4 B b hB (liftEdges Z Y) hPhys
    (liftVertexSet Z (U∪Aux)) hInsideL Ub hBudget hw1 hw2
  refine ⟨A,Y,hY,hEdges,hYLB,hAB,hAbs.1,hAbs.2.2,hAbs.2.1,?_,hRel⟩
  calc (A∪liftEdges Z Y).card ≤ A.card+(liftEdges Z Y).card := card_union_le _ _
    _ ≤ K*(4*k)*(4*(2*h-2).choose 2+6)+4*k := by
      apply Nat.add_le_add _ hYcard
      exact hAc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hYcard))
/-- Uniform native cell supply on the actual core subtype. The forbidden-edge
budget is measured against the core order, and no H3 assumption is made on its
ambient isolated-vertex extension. -/
theorem bounded_core_charge_cell (α β : ℝ) (h k : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ E n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (Z : Finset V), n₀ ≤ Fintype.card (Survivors Z) →
      CommonNbrCond H F α → HingeCond H F α h →
      CommonNbrCond (restrictedHost H Z) F β →
      ∀ (x : Sym2 (Survivors Z) → ℤ), x ∈ Composition.localProfile (restrictedHost H Z).G (restrictedHost H Z).lab F →
      edgeZeroExtend Z x ∈ lattice H F → (∑ e, |x e|) ≤ (k:ℤ) →
      ∀ (B : Finset (Sym2 V)) (b : ℕ), (∀ v, SelSimul.edeg B v ≤ b) →
      (b:ℝ) ≤ ε*Fintype.card (Survivors Z) →
      ∃ (A : Finset (Sym2 V)) (Y : Finset (Sym2 (Survivors Z))),
        Y.card ≤ 4*k ∧ Y ⊆ edges (restrictedHost H Z) ∧
        Disjoint (liftEdges Z Y) B ∧ Disjoint A B ∧ Disjoint A (liftEdges Z Y) ∧
        Basal H F (A∪liftEdges Z Y) ∧ Basal H F A ∧ (A∪liftEdges Z Y).card ≤ E ∧
        ind Y-x ∈ lattice (restrictedHost H Z) F := by
  obtain ⟨K,nA,hCell⟩ := core_integer_charge_cell α h hα
  let Ub := 5*k+3*(K*(4*k))+K*(4*k)*(2*h-2)+3*(K*(4*k))*(2*h-3)
  let a₀ : ℕ := 5*k+2
  let b₀ : ℕ := Ub+h+3
  let P : ℝ := 2^(Nat.choose h 2)
  have hP : 1 ≤ P := by dsimp [P]; exact one_le_pow₀ (by norm_num)
  have hPpos : 0 < P := by linarith
  let ε := min (β/8) (α/(40*P))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  refine ⟨ε,hε,K*(4*k)*(4*(2*h-2).choose 2+6)+4*k,
    nA+⌈4*(a₀:ℝ)/β⌉₊+⌈8*(b₀:ℝ)*P/α⌉₊+1,?_⟩
  intro V I _ H F Z hn h3 h4 hJ3 x hx hxG hnorm B b hB hb
  have hnpos : (0:ℝ) < Fintype.card (Survivors Z) := by exact_mod_cast (by omega : 0 < Fintype.card (Survivors Z))
  have hcardN : Fintype.card (Survivors Z) ≤ Fintype.card V := Fintype.card_subtype_le _
  have hna : nA ≤ Fintype.card V := (by omega : nA ≤ Fintype.card (Survivors Z)).trans hcardN
  have hαN : α*Fintype.card (Survivors Z) ≤ α*Fintype.card V :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcardN) hα.le
  have ha₀ : (a₀:ℝ) ≤ β/4*Fintype.card (Survivors Z) := by
    have hh : 4*(a₀:ℝ)/β ≤ Fintype.card (Survivors Z) := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈4*(a₀:ℝ)/β⌉₊ ≤ Fintype.card (Survivors Z)))
    rw [div_le_iff₀ hβ] at hh
    linarith
  have hb₀ : (b₀:ℝ)*P ≤ α/8*Fintype.card (Survivors Z) := by
    have hh : 8*(b₀:ℝ)*P/α ≤ Fintype.card (Survivors Z) := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈8*(b₀:ℝ)*P/α⌉₊ ≤ Fintype.card (Survivors Z)))
    rw [div_le_iff₀ hα] at hh
    linarith
  have hbβ : (b:ℝ) ≤ β/8*Fintype.card (Survivors Z) :=
    hb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnpos.le)
  have hbP : (b:ℝ)*P ≤ α/40*Fintype.card (Survivors Z) := by
    have hh := hb.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hnpos.le)
    have hh' := mul_le_mul_of_nonneg_right hh hPpos.le
    have he : α/(40*P)*Fintype.card (Survivors Z)*P = α/40*Fintype.card (Survivors Z) := by field_simp <;> ring
    rwa [he] at hh'
  have hb' : (b:ℝ) ≤ α/40*Fintype.card (Survivors Z) :=
    (le_mul_of_one_le_right (by positivity) hP).trans hbP
  have hb₀' : (b₀:ℝ) ≤ α/8*Fintype.card (Survivors Z) :=
    (le_mul_of_one_le_right (by positivity) hP).trans hb₀
  obtain ⟨U,hU,hroots⟩ := bounded_profile_roots x k hnorm
  have hwin : ((U.card+3*k+2*b+2:ℕ):ℝ) < β*Fintype.card (Survivors Z) := by
    have hu : ((U.card+3*k+2:ℕ):ℝ) ≤ a₀ := by exact_mod_cast (by dsimp [a₀]; omega : U.card+3*k+2 ≤ a₀)
    push_cast
    push_cast at hu
    nlinarith
  have hbudget : U.card+3*k+3*(K*(4*k))+K*(4*k)*(2*h-2)+3*(K*(4*k))*(2*h-3) ≤ Ub := by
    dsimp [Ub]
    omega
  have hw1 : (Ub:ℝ)+3+4*b < α*Fintype.card V := by
    have he : (Ub:ℝ)+3 ≤ b₀ := by exact_mod_cast (by dsimp [b₀]; omega : Ub+3 ≤ b₀)
    nlinarith
  have hw2 : ((Ub:ℝ)+1+h+5*b)*2^(Nat.choose h 2) ≤ α/2*Fintype.card V := by
    change ((Ub:ℝ)+1+h+5*b)*P ≤ _
    have he : (Ub:ℝ)+1+h ≤ b₀ := by dsimp [b₀]; push_cast; linarith
    have hh := mul_le_mul_of_nonneg_right he hPpos.le
    nlinarith
  exact hCell H F Z β hna h3 h4 hJ3 x U k hnorm hx hroots hxG B b Ub hB hwin hbudget hw1 hw2
end TypedTriangle.ChargePolar
