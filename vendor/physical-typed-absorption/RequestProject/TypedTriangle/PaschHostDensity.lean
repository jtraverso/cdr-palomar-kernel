module
public import RequestProject.TypedTriangle.CompositeHinge
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

def growthTriples (H : Host V I) (a b c : V) : Finset (Σ _ : V, Σ _ : V, V) :=
  (commonNbrs H (H.lab c) a b).sigma (fun w =>
    (commonNbrs H (H.lab b) a w).sigma (fun v => commonNbrs H (H.lab a) v w))

def tripleCube (Q : Finset V) : Finset (Σ _ : V, Σ _ : V, V) :=
  Q.sigma (fun _ => Q.sigma (fun _ => Q))

theorem commonNbr_card_lower {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) {a b c : V} (hT : IsAllowed H F {a,b,c}) :
    α*(Fintype.card V:ℝ) ≤ (commonNbrs H (H.lab c) a b).card := by
  obtain ⟨hab,hac,hbc⟩ := distinct_of_card_three hT.1
  have hF : ({H.lab a,H.lab b,H.lab c} : Multiset I) ∈ F := by
    have hh := hT.2.2
    rwa [Finset.insert_val_of_notMem (by simp [hab,hac]),
      Finset.insert_val_of_notMem (by simp [hbc])] at hh
  exact hH3 a b hab (H.lab c) hF

theorem growthTriple_allowed {H : Host V I} {F : Set (Multiset I)} {a b c : V}
    (hT : IsAllowed H F {a,b,c}) {z : Σ _ : V, Σ _ : V, V} (hz : z ∈ growthTriples H a b c) :
    IsAllowed H F {z.1,z.2.1,z.2.2} := by
  obtain ⟨hw,hv,hu⟩ := (by simpa only [growthTriples,mem_sigma] using hz :
    z.1 ∈ commonNbrs H (H.lab c) a b ∧
      z.2.1 ∈ commonNbrs H (H.lab b) a z.1 ∧ z.2.2 ∈ commonNbrs H (H.lab a) z.2.1 z.1)
  have h1 : IsAllowed H F {a,z.1,b} := by
    simpa only [Finset.pair_comm] using allowed_of_commonNbr hT hw
  have h2 : IsAllowed H F {z.2.1,z.1,a} := by
    have he : ({z.2.1,z.1,a}:Finset V) = {a,z.1,z.2.1} := by
      ext t
      simp [or_comm,or_left_comm,or_assoc]
    rw [he]
    exact allowed_of_commonNbr h1 hv
  simpa only [Finset.insert_comm] using allowed_of_commonNbr h2 hu

theorem growthTriples_card_lower {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) (hα : 0 ≤ α) {a b c : V} (hT : IsAllowed H F {a,b,c}) :
    (α*(Fintype.card V:ℝ))^3 ≤ (growthTriples H a b c).card := by
  let A := commonNbrs H (H.lab c) a b
  let B := fun w => commonNbrs H (H.lab b) a w
  let C := fun w v => commonNbrs H (H.lab a) v w
  let x := α*(Fintype.card V:ℝ)
  have hx : 0 ≤ x := mul_nonneg hα (Nat.cast_nonneg _)
  have hA : x ≤ (A.card:ℝ) := commonNbr_card_lower hH3 hT
  have hB : ∀ w ∈ A, x ≤ ((B w).card:ℝ) := by
    intro w hw
    have h1 : IsAllowed H F {a,w,b} := by
      simpa only [Finset.pair_comm] using allowed_of_commonNbr hT hw
    exact commonNbr_card_lower hH3 h1
  have hC : ∀ w ∈ A, ∀ v ∈ B w, x ≤ ((C w v).card:ℝ) := by
    intro w hw v hv
    have h1 : IsAllowed H F {a,w,b} := by
      simpa only [Finset.pair_comm] using allowed_of_commonNbr hT hw
    have h2 : IsAllowed H F {v,w,a} := by
      have he : ({v,w,a}:Finset V) = {a,w,v} := by
        ext t
        simp [or_comm,or_left_comm,or_assoc]
      rw [he]
      exact allowed_of_commonNbr h1 hv
    exact commonNbr_card_lower hH3 h2
  have hInner : ∀ w ∈ A, x^2 ≤ ∑ v ∈ B w, ((C w v).card:ℝ) := by
    intro w hw
    calc x^2 = x*x := by ring
      _ ≤ (B w).card*x := mul_le_mul_of_nonneg_right (hB w hw) hx
      _ = ∑ _v ∈ B w, x := by simp
      _ ≤ ∑ v ∈ B w, ((C w v).card:ℝ) := sum_le_sum (fun v hv => hC w hw v hv)
  change x^3 ≤ _
  simp only [growthTriples,Finset.card_sigma,Nat.cast_sum]
  calc x^3 = x*x^2 := by ring
    _ ≤ A.card*x^2 := mul_le_mul_of_nonneg_right hA (sq_nonneg x)
    _ = ∑ _w ∈ A, x^2 := by simp
    _ ≤ ∑ w ∈ A, ∑ v ∈ B w, ((C w v).card:ℝ) := sum_le_sum hInner

theorem growthTriples_card_upper {H : Host V I} {F : Set (Multiset I)} {a b c : V}
    (hT : IsAllowed H F {a,b,c}) : (growthTriples H a b c).card ≤ 27*(allowed H F).card := by
  have hSub : growthTriples H a b c ⊆ (allowed H F).biUnion tripleCube := by
    intro z hz
    refine mem_biUnion.mpr ⟨{z.1,z.2.1,z.2.2},?_,?_⟩
    · exact mem_filter.mpr ⟨mem_univ _,growthTriple_allowed hT hz⟩
    · simp [tripleCube]
  calc (growthTriples H a b c).card ≤ ∑ Q ∈ allowed H F, (tripleCube Q).card :=
      (card_le_card hSub).trans card_biUnion_le
    _ = ∑ _Q ∈ allowed H F, 27 := by
      apply sum_congr rfl
      intro Q hQ
      have hc := (mem_filter.mp hQ).2.1
      simp [tripleCube,Finset.card_sigma,hc]
    _ = 27*(allowed H F).card := by simp [Nat.mul_comm]

/-- H3 amplifies any permitted triangle to a uniform positive density of
permitted triangles. No additional host-density premise is used. -/
theorem allowed_density_of_triangle {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) (hα : 0 ≤ α) {a b c : V} (hT : IsAllowed H F {a,b,c}) :
    (α*(Fintype.card V:ℝ))^3/27 ≤ ((allowed H F).card:ℝ) := by
  have lo := growthTriples_card_lower hH3 hα hT
  have hi : ((growthTriples H a b c).card:ℝ) ≤ ((27*(allowed H F).card:ℕ):ℝ) :=
    Nat.cast_le.mpr (growthTriples_card_upper hT)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hi
  linarith only [lo,hi]

#print axioms growthTriples_card_lower
#print axioms growthTriples_card_upper
#print axioms allowed_density_of_triangle
end TypedTriangle.Pasch
