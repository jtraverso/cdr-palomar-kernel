module
public import RequestProject.TypedTriangle.PaschWeightedCoreComponent
public import RequestProject.TypedTriangle.PaschWeightedCoreAssembly
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SimpleGraph SelBridge SelTyped SelSimul S07V27
open TypedTriangle.ComponentRows S07V24 S07V25 S07V45
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I Ambient : Type} [Fintype V] [Fintype Ambient] [DecidableEq V] [DecidableEq Ambient]

/-- All active components of a real root are assembled with their retained
weighted selectors. The internal codegree shift is a fixed sixty. -/
theorem weighted_coreAvail_root
    {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (ι : V ↪ Ambient) (a q : ℝ) (ha : 0  <  a) (hq : 0  <  q)
    (m : ℕ) (hm : 0  <  m) (hOdd : Odd (m+1)) (W : Finset V)
    (hOrder : 2 ≤ q*Fintype.card V) (hWindow : (W.card:ℝ) ≤ 2*q*Fintype.card V)
    (hWindowLower : q*Fintype.card V/4 ≤ (W.card:ℝ))
    (hPaths : ∀ v x y, OrigAdm G lab F v x y →
      a*(Fintype.card V:ℝ)^m*q^m/4 ≤ (pathsIn (link G lab F v) m x y W).card)
    (X : SimpleGraph V) [DecidableRel X.Adj] (v : V)
    (hXl : ∀ u, X.Adj v u → ∃ y, (link G lab F v).Adj u y) {A ζ ρ r : ℕ}
    (hA : 200*m+8 ≤ A) (hdeg : X.degree v ≤ r)
    (hBud : ζ+(A+1)*r+10*r+m*(200*r) ≤ ⌊Vortex.windowRouteRate a q m*Fintype.card V⌋₊)
    (hρ : ((ρ+60:ℕ):ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V) :
    WeightedCoreAvail G lab F v (X.neighborFinset v) (rootAdm G lab F X v) A ζ ρ W ι
      (weightedCorePayShift (weightedCoreRoutePay a m (Fintype.card Ambient) W.card) 60) := by
  set N := X.neighborFinset v with hN
  have hNr : N.card ≤ r := by rw [hN, card_neighborFinset_eq_degree]; exact hdeg
  have hUeq : N = (activeComps G lab F v).biUnion (fun C => N ∩ C) := by
    ext u
    simp only [mem_biUnion, mem_inter]
    constructor
    · intro hu
      obtain ⟨y, hy⟩ := hXl u ((mem_neighborFinset _ _ _).1 hu)
      obtain ⟨h1, h2⟩ := mem_activeComps_of_link hy
      exact ⟨_, h1, hu, h2⟩
    · rintro ⟨C, -, hu, -⟩; exact hu
  have hdisj : ∀ C ∈ activeComps G lab F v, ∀ C' ∈ activeComps G lab F v, C ≠ C' →
      Disjoint (N ∩ C) (N ∩ C') := fun C hC C' hC' hne =>
    Disjoint.mono inter_subset_right inter_subset_right (activeComps_disjoint hC hC' hne)
  have hcomp : ∀ C ∈ activeComps G lab F v, WeightedCoreAvail G lab F v (N ∩ C) (compAdmC G lab F v C)
      A (ζ + (A + 1) * r) (ρ + 60) W ι
        (weightedCoreRoutePay a m (Fintype.card Ambient) W.card) := by
    intro C hC
    have hc : (N ∩ C).card ≤ r := (card_le_card inter_subset_left).trans hNr
    have h1 : m * (200 * (N ∩ C).card) ≤ m * (200 * r) :=
      Nat.mul_le_mul_left _ (by omega)
    exact weighted_coreAvail_component ι a q ha hq m hm hOdd W hOrder hWindow hWindowLower hPaths
      v C hC (N ∩ C) inter_subset_right hA (by omega) hρ
  have hbig := weighted_coreAvail_biUnion G lab F v (activeComps G lab F v) (fun C => N ∩ C)
    (compAdmC G lab F v) (ζ := ζ) (ρ := ρ) hdisj W ι
    (weightedCoreRoutePay a m (Fintype.card Ambient) W.card)
    (fun L => weightedCoreRoutePay_nonneg a ha m _ _ L) hcomp
    (by rw [← hUeq]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hNr) _) le_rfl
  rw [← hUeq] at hbig
  exact hbig

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.weighted_coreAvail_root
