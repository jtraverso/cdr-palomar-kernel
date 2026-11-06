module
public import RequestProject.TypedTriangle.PaschSupportPotential
public import RequestProject.TypedTriangle.PaschHostDensity
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace TypedTriangle.Pasch
variable {V K : Type*} [Fintype V] [Fintype K]

theorem exists_apex_total_cost_in_pool [DecidableEq V] (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (p q : K → V) (W : Finset V) (κ : ℝ)
    (hκ : 0 < κ) (hn : 0 < (Fintype.card V:ℝ)) (hW : κ*(Fintype.card V:ℝ) ≤ W.card) :
    ∃ x ∈ W, ((∑ k : K, rootedCount (insert {p k,q k,x} R) {p k,q k,x}):ℝ) ≤
      ((Fintype.card K:ℝ)*(L:ℝ)^3)/κ := by
  let P : Finset (Unit → V) := W.image (fun x _ => x)
  let i : K → Unit := fun _ => ()
  let a : ∀ k, ({j : Unit // j ≠ i k} → V) → V := fun k _ => p k
  let b : ∀ k, ({j : Unit // j ≠ i k} → V) → V := fun k _ => q k
  have hCard : P.card = W.card := by
    apply card_image_of_injective
    intro x y h
    exact congrFun h ()
  have hN : 0 < (Fintype.card (Unit → V):ℝ) := by simpa using hn
  have hP : κ*(Fintype.card (Unit → V):ℝ) ≤ P.card := by
    rw [hCard]
    simpa using hW
  obtain ⟨f,hf,hCost⟩ := exists_low_support_potential R L hL i a b P κ hκ hN hP
  obtain ⟨x,hx,hxf⟩ := mem_image.mp hf
  have hfx : f () = x := (congrFun hxf ()).symm
  refine ⟨x,hx,?_⟩
  simpa only [supportCompletionCost,i,a,b,hfx,Nat.cast_sum] using hCost

/-- H3 chooses one actual fresh apex paying the sum of all indicated
support-pair costs. The old family R is fixed before the apex is chosen. -/
theorem exists_low_total_cost_fresh_apex {I : Type*} {H : Host V I}
    {F : Set (Multiset I)} {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    {a b c : V} (hT : IsAllowed H F {a,b,c}) (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (p q : K → V) (B : Finset (Sym2 V)) (d : ℕ)
    (hdeg : ∀ v, degIn B v ≤ d) (Z : Finset V)
    (hwin : (Z.card:ℝ)+2*d ≤ α/2*Fintype.card V) :
    ∃ x : V, x ∉ Z ∧ IsAllowed H F {a,b,x} ∧ s(a,x) ∉ B ∧ s(b,x) ∉ B ∧
      ((∑ k : K, rootedCount (insert {p k,q k,x} R) {p k,q k,x}):ℝ) ≤
        ((Fintype.card K:ℝ)*(L:ℝ)^3)/(α/2) := by
  let bad := (Z ∪ nbrIn B a) ∪ nbrIn B b
  let W := commonNbrs H (H.lab c) a b \ bad
  have hbadNat : bad.card ≤ Z.card+2*d := by
    have ha := (card_nbrIn_le B a).trans (hdeg a)
    have hb := (card_nbrIn_le B b).trans (hdeg b)
    exact ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)).trans (by omega)
  have hbad : (bad.card:ℝ) ≤ (Z.card:ℝ)+2*d := by exact_mod_cast hbadNat
  have hcover : commonNbrs H (H.lab c) a b ⊆ W ∪ bad := by
    intro x hx
    by_cases hxb : x ∈ bad
    · exact mem_union_right _ hxb
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hx,hxb⟩)
  have hcountNat : (commonNbrs H (H.lab c) a b).card ≤ W.card+bad.card :=
    (card_le_card hcover).trans (card_union_le _ _)
  have hcount : ((commonNbrs H (H.lab c) a b).card:ℝ) ≤ W.card+bad.card := by
    exact_mod_cast hcountNat
  have hH3count := commonNbr_card_lower hH3 hT
  have hW : α/2*(Fintype.card V:ℝ) ≤ W.card := by
    linarith only [hcount,hH3count,hbad,hwin]
  have hnNat : 0 < Fintype.card V := by
    have hCard : 3 ≤ Fintype.card V := hT.1 ▸ card_le_univ ({a,b,c}:Finset V)
    omega
  have hn : (0:ℝ) < Fintype.card V := by exact_mod_cast hnNat
  obtain ⟨x,hx,hCost⟩ := exists_apex_total_cost_in_pool R L hL p q W (α/2) (by positivity) hn hW
  obtain ⟨hxCommon,hxBad⟩ := mem_sdiff.mp hx
  have hxZ : x ∉ Z := fun h => hxBad (mem_union_left _ (mem_union_left _ h))
  have hxA : s(a,x) ∉ B := by
    intro h
    exact hxBad (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩)))
  have hxB : s(b,x) ∉ B := by
    intro h
    exact hxBad (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩))
  exact ⟨x,hxZ,allowed_of_commonNbr hT hxCommon,hxA,hxB,hCost⟩

#print axioms exists_apex_total_cost_in_pool
#print axioms exists_low_total_cost_fresh_apex
end TypedTriangle.Pasch
