module
public import RequestProject.TypedTriangle.ExplicitNativeUniformCert
public import RequestProject.TypedTriangle.PreparedAbsorberSupply
public import RequestProject.TypedTriangle.PreparedUniformSupply
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.PreparedSupply.Explicit
open CorePayment Dispersal ExplicitCertificate ExplicitSample

def absorberCost (α : ℝ) (h : ℕ) : ℕ := uniformCertCost α h
def absorberOrder (α : ℝ) (h : ℕ) : ℕ := compressionOrder α h
def supplySize (α : ℝ) (h k : ℕ) : ℕ :=
  absorberCost α h * k * (4 * (2 * h - 2).choose 2 + 6)
def supplySupport (α : ℝ) (h k : ℕ) : ℕ :=
  let K := absorberCost α h
  2*k + 3*(K*k) + K*k*(2*h-2) + 3*(K*k)*(2*h-3)
def supplyBudget (α β : ℝ) (h : ℕ) : ℝ := S07V30.delta α β h
def supplyOrder (α : ℝ) (h k : ℕ) : ℕ := S07V30.n0 α (supplySupport α h k) h 0

theorem supplyBudget_pos {α β : ℝ} (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    0 < supplyBudget α β h := S07V30.delta_pos hα hβ h

theorem slot_absorber_explicit (α : ℝ) (h : ℕ) (hα : 0 < α) :
    let K := absorberCost α h
    let n₀ := absorberOrder α h
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
      n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
      ∀ (B : Finset (Sym2 V)) (d : ℕ), (∀ x, degIn B x ≤ d) → ∀ (P : Finset (Sym2 V)),
      IsPhysical H F P → ∀ (Z : Finset V), Inside Z P → ∀ (Ub : ℕ),
      Z.card + 3 * (K * P.card) + K * P.card * (2 * h - 2) +
        3 * (K * P.card) * (2 * h - 3) ≤ Ub →
      (Ub : ℝ) + 3 + 4 * d < α * Fintype.card V →
      ((Ub : ℝ) + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V →
      ∃ A, IsAbsorber H F A P ∧ Disjoint A B ∧
        A.card ≤ K * P.card * (4 * (2 * h - 2).choose 2 + 6) := by
  dsimp only
  intro V I _ H F hn hH3 hH4 B d hdeg P hP Z hPZ Ub hUb hw1 hw2
  exact slot_absorber_of_uniformCert hα hH3 hH4
    (uniformCert_of_H3H4_explicit α h hα H F hn hH3 hH4)
    B d hdeg P hP Z hPZ Ub hUb hw1 hw2


theorem prepared_absorber_window_explicit (α : ℝ) (h : ℕ) (hα : 0 < α) :
    let K := absorberCost α h
    let N := absorberOrder α h
    ∀ {V I : Type} [Fintype V] (H : Host V I)
      (F : Set (Multiset I)) (β : ℝ),
      PreparedCore H.G H.lab F α h N β →
      ∀ (P : Finset (Sym2 V)), IsPhysical H F P →
      ∀ (Z : Finset V), (Z.card:ℝ) ≤ β*Fintype.card V →
      (∀ e ∈ P, ∀ v ∈ e, v ∉ Z) →
      ∀ (B : Finset (Sym2 V)) (d Ub : ℕ), (∀ v, degIn B v ≤ d) →
      (support P).card + 3*(K*P.card) + K*P.card*(2*h-2) +
        3*(K*P.card)*(2*h-3) ≤ Ub →
      (Ub:ℝ)+3+4*d < α*Fintype.card (Survivors Z) →
      ((Ub:ℝ)+1+h+5*d)*2^(Nat.choose h 2) ≤ α/2*Fintype.card (Survivors Z) →
      ∃ A, IsAbsorber H F A P ∧ Disjoint A B ∧
        A.card ≤ K*P.card*(4*(2*h-2).choose 2+6) ∧
        ∀ e ∈ A, ∀ v ∈ e, v ∉ Z := by
  dsimp only
  let K := absorberCost α h
  let N := absorberOrder α h
  intro V I _ H F β Pc P hP Z hZ hav B d Ub hBd hUb hw1 hw2
  have h3 : CommonNbrCond (restrictedHost H Z) F α := by
    change SparseEdge.CommonNbrCond (restrictedHost H Z).G (restrictedHost H Z).lab F α
    rw [restrictedHost_G_eq_dispersal,restrictedHost_lab_eq_dispersal]
    exact Pc.h3 Z hZ
  have h4 : HingeCond (restrictedHost H Z) F α h := by
    change SparseEdge.HingeCond (restrictedHost H Z).G (restrictedHost H Z).lab F α h
    rw [restrictedHost_G_eq_dispersal,restrictedHost_lab_eq_dispersal]
    exact Pc.h4 Z hZ
  have hsize : (pullEdges Z P).card ≤ P.card := by
    rw [pullEdges,card_preimage]
    exact card_filter_le _ _
  have hroot : ((support P).subtype (fun v => v ∉ Z)).card ≤ (support P).card := by
    rw [card_subtype]
    exact card_filter_le _ _
  have hb : ∀ v, degIn (pullEdges Z B) v ≤ d := by
    intro v
    have hh := degree_pull_le Z B v
    simp only [edeg_eq_classical] at hh
    have hh' : degIn (pullEdges Z B) v ≤ degIn B v.1 := by
      simpa only [degIn,SelSimul.edeg] using hh
    exact hh'.trans (hBd v.1)
  have hp := prepared_physical_pull Pc P hP Z hZ hav
  have hu : ((support P).subtype (fun v => v ∉ Z)).card +
      3*(K*(pullEdges Z P).card) + K*(pullEdges Z P).card*(2*h-2) +
      3*(K*(pullEdges Z P).card)*(2*h-3) ≤ Ub := by
    have hK := Nat.mul_le_mul_left K hsize
    have h1 := Nat.mul_le_mul_left 3 hK
    have h2 := Nat.mul_le_mul_right (2*h-2) hK
    have h3 := Nat.mul_le_mul_right (2*h-3) h1
    dsimp only [K] at hK h1 h2 h3 ⊢
    omega
  obtain ⟨A,hA,hAB,hcard⟩ := slot_absorber_explicit α h hα (restrictedHost H Z) F (Pc.order Z hZ) h3 h4
    (pullEdges Z B) d hb (pullEdges Z P) hp
    ((support P).subtype (fun v => v ∉ Z)) (support_pull_inside Z P) Ub hu hw1 hw2
  refine ⟨liftEdges Z A,absorber_lift Z hav hA,?_,?_,liftEdges_avoids Z A⟩
  · apply disjoint_left.mpr
    intro e he heB
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact disjoint_left.mp hAB hf (mem_preimage.mpr heB)
  · exact card_image_le.trans (hcard.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hsize)))

theorem prepared_uniform_supply_explicit (α : ℝ) (h k : ℕ) (hα : 0 < α) :
    let N := absorberOrder α h
    let s := supplySize α h k
    ∀ β : ℝ, 0 < β →
    let δ := supplyBudget α β h
    let n₀ := supplyOrder α h k
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → PreparedCore H.G H.lab F α h N β →
        ∀ P : Finset (Sym2 V), P.card ≤ k → IsPhysical H F P →
        S07V28.RobustAbsorberSupply H.G H.lab F P s
          ⌊δ*Fintype.card V⌋₊ ⌊δ*Fintype.card V⌋₊ := by
  dsimp only
  let K := absorberCost α h
  let s := K*k*(4*(2*h-2).choose 2+6)
  let U := 2*k + 3*(K*k) + K*k*(2*h-2) + 3*(K*k)*(2*h-3)
  intro β hβ
  let δ := supplyBudget α β h
  have hwin := S07V30.deletion_window hα hβ U h
  intro V I _ H F hn Pc P hk hP B hBd S hS
  let Z := S \ support P
  have hz : Z.card ≤ ⌊δ*Fintype.card V⌋₊ := (card_le_card sdiff_subset).trans hS
  have hw := hwin (Fintype.card V) (Fintype.card (Survivors Z)) Z.card
    ⌊δ*Fintype.card V⌋₊ hn (card_survivors_add_card Z) hz le_rfl
  have hav : ∀ e ∈ P, ∀ v ∈ e, v ∉ Z := by
    intro e he v hv hvZ
    exact (mem_sdiff.mp hvZ).2 (mem_filter.mpr ⟨mem_univ _,e,he,hv⟩)
  have hsup : (support P).card ≤ 2*k :=
    (S07V28.card_support_le P).trans (Nat.mul_le_mul_left 2 hk)
  have hU : (support P).card + 3*(K*P.card) + K*P.card*(2*h-2) +
      3*(K*P.card)*(2*h-3) ≤ U := by
    dsimp [U]
    gcongr
  obtain ⟨A,hA,hAB,hcard,havoid⟩ := prepared_absorber_window_explicit α h hα H F β Pc P hP Z hw.1 hav B
    ⌊δ*Fintype.card V⌋₊ U hBd hU hw.2.2.1 hw.2.2.2
  refine ⟨A,hA,hAB,hcard.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hk)),?_⟩
  intro v hv hvS
  by_contra hvP
  obtain ⟨_,e,he,hve⟩ := mem_filter.mp hv
  exact havoid e he v hve (mem_sdiff.mpr ⟨hvS,hvP⟩)

#print axioms slot_absorber_explicit
#print axioms prepared_absorber_window_explicit
#print axioms prepared_uniform_supply_explicit
end TypedTriangle.PreparedSupply.Explicit
