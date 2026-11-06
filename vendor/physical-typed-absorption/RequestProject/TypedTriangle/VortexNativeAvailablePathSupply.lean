/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexAutomaticCleanRawPathsBeforeRate
public import RequestProject.TypedTriangle.VortexWindowPathTrim
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24 S07V25
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex
open CorePaid ComponentRows

/-- Native original-root paths remain plentiful after an arbitrary small
fixed deletion of their auxiliaries. All constants precede every sampling
rate, and the two fixed roots may themselves belong to the deletion set. -/
theorem native_available_path_supply (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ (m : ℕ) (a δ : ℝ) (n₀ : ℕ),
      0 < m ∧ 0 < a ∧ 0 < δ ∧ Odd (m+1) ∧ 3 ≤ m+1 ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∀ A : Finset V, (A.card:ℝ) ≤ δ*Fintype.card V →
        ∀ v x y, AdmPair (activeComps H.G H.lab F)
          (fun v C => IsBip H.G H.lab F (v,C)) (colG H.G H.lab F) v x y →
          (a/2)*(Fintype.card V:ℝ)^m ≤
            (pathsIn (link H.G H.lab F v) m x y (univ \ A)).card := by
  let κ := kappaOf α h
  have hκ : 0 < κ := kappaOf_pos hα h
  let m := mOf α κ
  let a := aOf α κ
  have hm : 0 < m := by dsimp [m,mOf]; positivity
  have ha : 0 < a := by
    have hp : 0 < min α 1 := lt_min hα one_pos
    dsimp [a,aOf]
    positivity
  have hodd : Odd (m+1) := by
    obtain ⟨hk,_⟩ := kOf_spec hα hκ
    have heq : m+1 = kOf α κ + 2 := by dsimp [m,mOf]
    rw [heq]
    exact hk.add_even even_two
  have ht3 : 3 ≤ m+1 := by
    obtain ⟨hk,_⟩ := kOf_spec hα hκ
    dsimp [m,mOf]
    obtain ⟨j,hj⟩ := hk
    omega
  let δ := a/(4*(m:ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let n₀ := max (n0Of α κ) (n1Of α)
  refine ⟨m,a,δ,n₀,hm,ha,hδ,hodd,ht3,?_⟩
  intro V I _ H F hn h3 h4 A hA v x y hadm
  letI : DecidableEq V := Classical.decEq _
  letI : ∀ v, DecidableRel (link H.G H.lab F v).Adj := fun _ => Classical.decRel _
  have hI := activeComps_interface hα h3 h4 ((le_max_right _ _).trans hn)
  have hpaths : a*(Fintype.card V:ℝ)^m ≤
      (pathsLen (link H.G H.lab F v) (m+1) x y).card := by
    obtain ⟨C,hC,hx,hy,hxy,hcol⟩ := hadm
    exact link_paths_of_interface α κ hα hκ (link H.G H.lab F v)
      (Fintype.card V) ((le_max_left _ _).trans hn) rfl C
      (IsBip H.G H.lab F (v,C)) (colG H.G H.lab F v)
      (hI v C hC) x y hx hy hxy hcol
  have hFull : pathsIn (link H.G H.lab F v) m x y univ =
      pathsLen (link H.G H.lab F v) (m+1) x y := by
    simp [pathsIn]
  have hTrim := paths_in_trim_count (link H.G H.lab F v) m x y univ A
  rw [hFull,Finset.card_univ] at hTrim
  have hTrimR : ((pathsLen (link H.G H.lab F v) (m+1) x y).card:ℝ) ≤
      (pathsIn (link H.G H.lab F v) m x y (univ \ A)).card +
        (A.card:ℝ)*(m:ℝ)*(Fintype.card V:ℝ)^(m-1) := by exact_mod_cast hTrim
  have hδm : δ*(m:ℝ) = a/4 := by dsimp [δ]; field_simp
  have hPower : (Fintype.card V:ℝ)^(m-1)*(Fintype.card V:ℝ) =
      (Fintype.card V:ℝ)^m := by rw [← pow_succ,Nat.sub_add_cancel hm]
  have hLoss : (A.card:ℝ)*(m:ℝ)*(Fintype.card V:ℝ)^(m-1) ≤
      (a/4)*(Fintype.card V:ℝ)^m := by
    calc
      (A.card:ℝ)*(m:ℝ)*(Fintype.card V:ℝ)^(m-1) =
          (A.card:ℝ)*((m:ℝ)*(Fintype.card V:ℝ)^(m-1)) := by ring
      _ ≤ (δ*Fintype.card V)*((m:ℝ)*(Fintype.card V:ℝ)^(m-1)) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ = (a/4)*(Fintype.card V:ℝ)^m := by rw [← hδm,← hPower]; ring
  have hPos : 0 ≤ a*(Fintype.card V:ℝ)^m := by positivity
  nlinarith only [hpaths,hTrimR,hLoss,hPos]

#print axioms native_available_path_supply
end TypedTriangle.Vortex
