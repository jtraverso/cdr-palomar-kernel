/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ClonedEGJ
public import RequestProject.TypedTriangle.SeedMultiplicity
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedClone

theorem project_matching {E ι : Type*} [Fintype E] [Fintype ι]
    (P : ι → Finset E) (m : ι → ℕ) (hP : ∀ i, (P i).Nonempty)
    (C : Finset (Copy m))
    (hC : (C : Set (Copy m)).PairwiseDisjoint (fun c => P c.1)) :
    ∃ Q : Finset ι, (Q : Set ι).PairwiseDisjoint P ∧
      ∀ w : ι → ℝ, (∑ i ∈ Q, w i)=∑ c ∈ C, w c.1 := by
  have hinj : Set.InjOn (fun c : Copy m => c.1) C := by
    intro c hc d hd heq
    by_contra hcd
    have hdj := hC hc hd hcd
    obtain ⟨e,he⟩ := hP c.1
    exact disjoint_left.mp hdj he (by simpa only [←heq] using he)
  refine ⟨C.image Sigma.fst,?_,?_⟩
  · intro i hi j hj hij
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hi
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hj
    exact hC hc hd (fun h => hij (congrArg Sigma.fst h))
  · intro w
    rw [sum_image hinj]

/-- Combine EGJ's integral matching with exact rounding-error estimates for
an arbitrary real fractional profile. All numerical caps concern the explicit
ceil multiplicities; the matching and its monitored weights are constructed. -/
theorem fractional_matching_of_caps (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (r : ℕ) (hr : 1≤r) :
    ∃ D₀ : ℝ, ∀ D p a : ℝ, D₀≤D → 1≤D → 0≤p → p≤D → 0≤a →
    ∀ (E ι : Type) [Fintype E] [Fintype ι] (P : ι → Finset E) (φ : ι → ℝ),
      (∀ i, (P i).card=r) → (∀ i, 0≤φ i) → (∀ i, 1≤a*φ i) →
      (∀ e, ((∑ i, if e∈P i then seedMultiplicity p φ i else 0 : ℕ):ℝ)≤D) →
      (∀ e f, e≠f → ((∑ i, if e∈P i ∧ f∈P i then seedMultiplicity p φ i else 0 : ℕ):ℝ)≤D^(1-δ)) →
      ((∑ i, seedMultiplicity p φ i : ℕ):ℝ)≤Real.exp (D^((δ/(50*(r+1)^2))^2)) →
      ∀ (κ : Type) [Fintype κ] (W : κ → ι → ℝ), (∀ k i, 0≤W k i) →
      (Fintype.card κ:ℝ)≤Real.exp (D^((δ/(50*(r+1)^2))^2)) →
      ∃ Q : Finset ι, (Q : Set ι).PairwiseDisjoint P ∧
        ∀ k, (∀ i, W k i*D^(1+δ)≤p*(∑ j, φ j*W k j)) →
          |(∑ i ∈ Q, W k i)-(∑ i, φ i*W k i)|≤
            (D^(-(δ/(50*(r+1)^2)))*(p+a)/D+(D-p+a)/D)*(∑ i, φ i*W k i) := by
  obtain ⟨D₀,hMatch⟩ := matching_from_integer_multiplicities δ hδ hδ1 r hr
  refine ⟨D₀,?_⟩
  intro D p a hD₀ hD hp hpD ha E ι _ _ P φ hcard hφ hfloor hdeg hcod hsize κ _ W hW hκ
  let m := seedMultiplicity p φ
  obtain ⟨C,hC,hweights⟩ := hMatch D hD₀ hD E ι P m hcard hdeg hcod hsize κ W hW hκ
  have hP : ∀ i, (P i).Nonempty := fun i => card_pos.mp (by rw [hcard]; omega)
  obtain ⟨Q,hQ,hQC⟩ := project_matching P m hP C hC
  refine ⟨Q,hQ,?_⟩
  intro k hmass
  have hS : 0≤∑ i, φ i*W k i := sum_nonneg fun i _ => mul_nonneg (hφ i) (hW k i)
  have hDpos : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hξ : 0≤D^(-(δ/(50*(r+1)^2))) := Real.rpow_nonneg hDpos.le _
  obtain ⟨hlo,hhi⟩ := multiplicity_mass_factor p a hp φ (W k) hφ (hW k) hfloor
  have hmatch := hweights k (by
    intro i _
    exact (hmass i).trans hlo)
  rw [←hQC (W k)] at hmatch
  have hround := multiplicity_normalization_error ha hDpos hpD hS hlo hhi
  have hmasshi : (∑ i, (m i:ℝ)*W k i)/D≤((p+a)/D)*(∑ i, φ i*W k i) := by
    calc (∑ i, (m i:ℝ)*W k i)/D≤((p+a)*(∑ i, φ i*W k i))/D :=
        div_le_div_of_nonneg_right hhi hDpos.le
      _ = _ := by ring
  calc |(∑ i ∈ Q, W k i)-(∑ i, φ i*W k i)|
      ≤ |(∑ i ∈ Q, W k i)-(∑ i, (m i:ℝ)*W k i)/D|+
        |(∑ i, (m i:ℝ)*W k i)/D-(∑ i, φ i*W k i)| := abs_sub_le _ _ _
    _ ≤ D^(-(δ/(50*(r+1)^2)))*((∑ i, (m i:ℝ)*W k i)/D)+
        ((D-p+a)/D)*(∑ i, φ i*W k i) := add_le_add hmatch hround
    _ ≤ (D^(-(δ/(50*(r+1)^2)))*(p+a)/D+(D-p+a)/D)*(∑ i, φ i*W k i) := by
      have hh := mul_le_mul_of_nonneg_left hmasshi hξ
      calc _ ≤ D^(-(δ/(50*(r+1)^2)))*(((p+a)/D)*(∑ i, φ i*W k i))+
          ((D-p+a)/D)*(∑ i, φ i*W k i) := add_le_add hh le_rfl
        _ = _ := by ring

end TypedTriangle.WeightedClone
