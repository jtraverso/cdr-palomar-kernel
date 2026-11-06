module
public import RequestProject.TypedTriangle.PaschAmbientStockPayment
public import RequestProject.TypedTriangle.PaschHostDensity
public import RequestProject.TypedTriangle.CorePaidLayer
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open SelSimul Envelope
variable {V I Ambient : Type*} [Fintype V] [Fintype Ambient]

/-- Pay a boundary using actual H3 pools. The literal decomposition is kept,
and its potential is measured in the ambient carrier. The stock supply does
not occur in this construction. -/
theorem envelope_of_H3_with_ambient_pasch (ι : V ↪ Ambient)
    {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (E B : Finset (Sym2 V)) {r b q : ℕ} (hq : 0 < q)
    (hn : 0 < Fintype.card V)
    (hE : ∀ v, edeg E v ≤ r) (hB : ∀ v, edeg B v ≤ b)
    (htri : ∀ e ∈ E, HasTri H F e)
    (hwin : (E.card : ℝ)/(q : ℝ)+2*((b+3*r+2*q : ℕ) : ℝ) ≤
      (α/2)*Fintype.card V)
    (Rfixed : Finset (Finset Ambient)) (L : ℕ)
    (hL : PairCodegreeBound Rfixed L) :
    ∃ (W : Finset (Sym2 V)) (D : Finset (Finset V)),
      Disjoint W (E∪B) ∧ IsDecomposition H F (E∪W) D ∧
      (∀ v, edeg W v ≤ 2*(r+q)) ∧
      (count (Rfixed∪mapConfiguration ι D) : ℝ) ≤ count Rfixed+
        2*(E.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card V)*
          ((L+1 : ℕ) : ℝ)^3/α := by
  let X := edges H\(E∪B)
  let Cand : Sym2 V → Finset V := fun e => univ.filter (fun w =>
    w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧ ∀ x ∈ e, s(x,w) ∈ X)
  have hU : ∀ e ∈ E, ¬e.IsDiag := by
    intro e he
    obtain ⟨a,b,c,heq,hT⟩ := (htri e he).exists_tri
    rw [heq,Sym2.mk_isDiag_iff]
    exact (distinct_of_card_three hT.1).1
  have hCand : ∀ e ∈ E, ∀ w ∈ Cand e,
      w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧ ∀ x ∈ e, s(x,w) ∈ X := by
    intro e he w hw
    exact (mem_filter.mp hw).2
  have hCX : ∀ e ∈ E, α*Fintype.card V-2*((b+r : ℕ) : ℝ) ≤ (Cand e).card := by
    intro e he
    induction e using Sym2.ind with
    | h a b' =>
      obtain ⟨c,hT⟩ := CorePaid.hasTri_roots (htri s(a,b') he)
      let Bad := nbrIn (E∪B) a ∪ nbrIn (E∪B) b'
      let Good := commonNbrs H (H.lab c) a b'\Bad
      have hd : ∀ v, degIn (E∪B) v ≤ b+r := by
        intro v
        have hh := edeg_union_le E B v
        have h1 := hE v
        have h2 := hB v
        change edeg (E∪B) v ≤ b+r
        omega
      have hBad : Bad.card ≤ 2*(b+r) := by
        exact (card_union_le _ _).trans (by
          have ha := (card_nbrIn_le (E∪B) a).trans (hd a)
          have hb := (card_nbrIn_le (E∪B) b').trans (hd b')
          omega)
      have hSub : Good ⊆ Cand s(a,b') := by
        intro w hw
        obtain ⟨hw,hbad⟩ := mem_sdiff.mp hw
        have hAw := allowed_of_commonNbr hT hw
        obtain ⟨hab,haw,hbw⟩ := distinct_of_card_three hAw.1
        have haB : s(a,w) ∉ E∪B := fun hh => hbad (mem_union_left _
          (mem_filter.mpr ⟨mem_univ _,hh⟩))
        have hbB : s(b',w) ∉ E∪B := fun hh => hbad (mem_union_right _
          (mem_filter.mpr ⟨mem_univ _,hh⟩))
        apply mem_filter.mpr
        refine ⟨mem_univ _,?_,?_,?_⟩
        · simp only [Sym2.mem_iff]
          exact fun hh => hh.elim (fun h => haw h.symm) (fun h => hbw h.symm)
        · have hSet : insert w s(a,b').toFinset=({a,b',w} : Finset V) := by
            ext z
            simp [Sym2.toFinset_mk_eq,or_comm,or_left_comm,or_assoc]
          rw [hSet]
          exact hAw
        · intro x hx
          rcases Sym2.mem_iff.mp hx with rfl | rfl
          · exact mem_sdiff.mpr ⟨triEdges_subset_edges hAw
              (mem_triEdges.mpr ⟨by simp,by simp,haw⟩),haB⟩
          · exact mem_sdiff.mpr ⟨triEdges_subset_edges hAw
              (mem_triEdges.mpr ⟨by simp,by simp,hbw⟩),hbB⟩
      have hCover : (commonNbrs H (H.lab c) a b').card ≤ Good.card+Bad.card := by
        have hs : commonNbrs H (H.lab c) a b' ⊆ Good∪Bad := by
          intro w hw
          by_cases hb : w∈Bad
          · exact mem_union_right _ hb
          · exact mem_union_left _ (mem_sdiff.mpr ⟨hw,hb⟩)
        exact (card_le_card hs).trans (card_union_le _ _)
      have hCoverR : ((commonNbrs H (H.lab c) a b').card : ℝ) ≤ Good.card+Bad.card := by exact_mod_cast hCover
      have hBadR : (Bad.card : ℝ) ≤ 2*((b+r : ℕ) : ℝ) := by exact_mod_cast hBad
      have hGoodR : (Good.card : ℝ) ≤ (Cand s(a,b')).card := Nat.cast_le.mpr (card_le_card hSub)
      have hPool := commonNbr_card_lower hH3 hT
      linarith only [hCoverR,hBadR,hGoodR,hPool]
  have hMargin : ∀ e ∈ E,
      (E.card : ℝ)+(q : ℝ)*(2*(r+2*q) : ℕ)+(q : ℝ)*(α/2)*Fintype.card V ≤
        (q : ℝ)*(Cand e).card := by
    intro e he
    have hqR : (0 : ℝ)<q := Nat.cast_pos.mpr hq
    have hScaled := (div_le_iff₀ hqR).mp (show (E.card : ℝ)/(q : ℝ) ≤
        (α/2)*Fintype.card V-2*((b+3*r+2*q : ℕ) : ℝ) by linarith only [hwin])
    have hPool := mul_le_mul_of_nonneg_left (hCX e he) hqR.le
    push_cast at hScaled hPool ⊢
    nlinarith only [hScaled,hPool]
  have hEmpty : IsPacking H F (∅ : Finset (Finset V)) := ⟨by simp,by simp⟩
  have hEX : Disjoint E X := disjoint_left.mpr (by
    intro e he hx
    exact (mem_sdiff.mp hx).2 (mem_union_left _ he))
  obtain ⟨D,hD,_,hCov,hSub,hDeg,hStat⟩ :=
    cover_down_with_ambient_fixed_universe_pasch ι H F ∅ hEmpty Rfixed
      (by simp [mapConfiguration]) L hL E X hEX (by simp) hU Cand hCand
      hq (α/2) (half_pos hα) hn hE hMargin
  let W := D.biUnion triEdges\E
  have hEq : E∪W=D.biUnion triEdges := by
    dsimp only [W]
    ext e
    simp only [mem_union,mem_sdiff]
    constructor
    · intro he
      rcases he with he | he
      · exact hCov he
      · exact he.1
    · intro he
      by_cases hh : e∈E <;> tauto
  have hAvoid : Disjoint W (E∪B) := disjoint_left.mpr (by
    intro e he hp
    obtain ⟨heD,heE⟩ := mem_sdiff.mp he
    rcases mem_union.mp (hSub heD) with hh | hh
    · exact heE hh
    · exact (mem_sdiff.mp hh).2 hp)
  refine ⟨W,D,hAvoid,?_,?_,?_⟩
  · rw [hEq]
    exact hD.isDecomposition
  · intro v
    have hh : edeg (D.biUnion triEdges) v ≤ 2*(r+q) := by
      change ((D.biUnion triEdges).filter (v∈·)).card ≤ _
      have hv := hDeg v
      omega
    exact (edeg_mono sdiff_subset v).trans hh
  · have hCostEq : (E.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card V)*
        ((L+1 : ℕ) : ℝ)^3/(α/2) =
        2*(E.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card V)*
        ((L+1 : ℕ) : ℝ)^3/α := by ring
    simpa only [hCostEq] using hStat
end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.envelope_of_H3_with_ambient_pasch
