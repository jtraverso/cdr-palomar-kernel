/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.Pseudorandom.ExplicitTheorem12
public import RequestProject.TypedTriangle.ExplicitPackingNumerics
public import RequestProject.TypedTriangle.DiffuseWeightedPacking
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedClone.Explicit

theorem matching_from_integer_multiplicities_explicit (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (r : ℕ) (hr : 1≤r) :
    ∀ D : ℝ, Pseudorandom.Explicit.egjCut δ (r+1)≤D → 1≤D →
    ∀ (E ι : Type) [Fintype E] [Fintype ι] (P : ι → Finset E) (m : ι → ℕ),
      (∀ i, (P i).card=r) →
      (∀ e, ((∑ i, if e∈P i then m i else 0 : ℕ):ℝ)≤D) →
      (∀ e f, e≠f → ((∑ i, if e∈P i ∧ f∈P i then m i else 0 : ℕ):ℝ)≤D^(1-δ)) →
      ((∑ i, m i : ℕ):ℝ)≤Real.exp (D^((δ/(50*(r+1)^2))^2)) →
      ∀ (κ : Type) [Fintype κ] (W : κ → ι → ℝ),
      (∀ k i, 0≤W k i) →
      (Fintype.card κ:ℝ)≤Real.exp (D^((δ/(50*(r+1)^2))^2)) →
      ∃ C : Finset (Copy m),
        (C : Set (Copy m)).PairwiseDisjoint (fun c => P c.1) ∧
        ∀ k, (∀ i, 0 < m i → W k i*D^(1+δ)≤∑ j, (m j:ℝ)*W k j) →
          |(∑ c ∈ C, W k c.1)-(∑ i, (m i:ℝ)*W k i)/D|≤
            D^(-(δ/(50*(r+1)^2)))*((∑ i, (m i:ℝ)*W k i)/D) := by
  have hEGJ := Pseudorandom.Explicit.theorem_1_2_explicit δ hδ hδ1 (r+1) (by omega)
  intro D hD₀ hD E ι _ _ P m hcard hdeg hcode hsize κ _ W hW hκ
  have hpow : 1≤D^(1-δ) := Real.one_le_rpow hD (by linarith)
  have hdegree : ∀ v : E ⊕ Copy m,
      (Pseudorandom.degree (hypergraph P m) v:ℝ)≤D := by
    intro v
    cases v with
    | inl e => simpa only [degree_left] using hdeg e
    | inr c => simpa only [degree_right,Nat.cast_one] using hD
  have hcodegree : ∀ u v : E ⊕ Copy m, u≠v →
      (Pseudorandom.codegree (hypergraph P m) u v:ℝ)≤D^(1-δ) := by
    intro u v huv
    cases u with
    | inl e =>
      cases v with
      | inl f => exact (by simpa only [codegree_left] using hcode e f (by simpa using huv))
      | inr c => exact (show (Pseudorandom.codegree (hypergraph P m) (Sum.inl e) (Sum.inr c):ℝ)≤1 by exact_mod_cast codegree_mixed_le P m e c).trans hpow
    | inr c =>
      cases v with
      | inl e =>
        have heq : Pseudorandom.codegree (hypergraph P m) (Sum.inr c) (Sum.inl e)=
            Pseudorandom.codegree (hypergraph P m) (Sum.inl e) (Sum.inr c) := by
          simp only [Pseudorandom.codegree,and_comm]
        rw [heq]
        exact (show (Pseudorandom.codegree (hypergraph P m) (Sum.inl e) (Sum.inr c):ℝ)≤1 by exact_mod_cast codegree_mixed_le P m e c).trans hpow
      | inr d =>
        rw [codegree_right_eq_zero P m (by simpa using huv),Nat.cast_zero]
        exact le_trans zero_le_one hpow
  obtain ⟨M,hMH,hM,hweights⟩ := hEGJ D hD₀ (E ⊕ Copy m) (hypergraph P m)
    (hypergraph_uniform P m hcard) hdegree hcodegree (by simpa only [hypergraph_card,Nat.cast_add,Nat.cast_one] using hsize)
    κ (fun k => liftedWeight P m (W k)) (by
      intro k T hT
      obtain ⟨c,_,rfl⟩ := mem_image.mp hT
      rw [liftedWeight_packet]
      exact hW k c.1) (by simpa only [Nat.cast_add,Nat.cast_one] using hκ)
  obtain ⟨C,hMC,hDis,hWC⟩ := extract_matching P m hMH hM
  refine ⟨C,hDis,?_⟩
  intro k hmass
  have hbound := hweights k (by
    intro T hT
    obtain ⟨c,_,rfl⟩ := mem_image.mp hT
    rw [liftedWeight_packet,weight_hypergraph]
    exact hmass c.1 (Nat.zero_lt_of_lt c.2.2))
  rw [hWC (W k),weight_hypergraph] at hbound
  simpa only [Nat.cast_add,Nat.cast_one] using hbound

theorem fractional_matching_of_caps_explicit (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (r : ℕ) (hr : 1≤r) :
    ∀ D p a : ℝ, Pseudorandom.Explicit.egjCut δ (r+1)≤D → 1≤D → 0≤p → p≤D → 0≤a →
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
  have hMatch := matching_from_integer_multiplicities_explicit δ hδ hδ1 r hr
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

theorem diffuse_weighted_matching_explicit (C c η : ℝ) (q : ℕ)
    (hC : 0 < C) (hc : 0 < c) (hη : 0 < η) :
    ∀ n : ℝ, cloneCut C c η (Pseudorandom.Explicit.egjCut (1/4) 4) q ≤ n →
      ∀ (E ι κ : Type) [Fintype E] [Fintype ι] [Fintype κ]
        (P : ι → Finset E) (φ : ι → ℝ) (W : κ → ι → ℝ),
      (Fintype.card E:ℝ) ≤ n^2 →
      (∀ i, (P i).card = 3) →
      (∀ i, 1/(C*n) ≤ φ i ∧ φ i ≤ C/n) →
      (∀ e, ∑ i, (if e ∈ P i then φ i else 0) ≤ 1) →
      (∀ e f, e ≠ f → (univ.filter fun i => e ∈ P i ∧ f ∈ P i).card ≤ 1) →
      (Fintype.card κ:ℝ) ≤ n^q →
      (∀ k i, 0 ≤ W k i ∧ W k i ≤ 1) →
      (∀ k, c*n ≤ ∑ i, φ i*W k i) →
      ∃ Q : Finset ι, (Q : Set ι).PairwiseDisjoint P ∧
        ∀ k, |(∑ i ∈ Q, W k i)-(∑ i, φ i*W k i)| ≤ η*(∑ i, φ i*W k i) := by
  let D₀ := Pseudorandom.Explicit.egjCut (1/4) 4
  have hMatch := fractional_matching_of_caps_explicit (1/4) (by norm_num) (by norm_num) 3 (by norm_num)
  have hn₀ := clone_numerics_explicit C c η D₀ q hC.le hc hη
  intro n hn E ι κ _ _ _ P φ W hE hcard hφ hload hlin hκ hW hmass
  obtain ⟨hn1,hD₀,hD1,hcode,hsize,htests,hmasscap,herror⟩ := hn₀ n hn
  have hnpos : 0 < n := by linarith
  have hφ₀ : ∀ i, 0 ≤ φ i := fun i => (by positivity : (0:ℝ) ≤ 1/(C*n)).trans (hφ i).1
  have hfloor : ∀ i, 1 ≤ (C*n)*φ i := by
    intro i
    have hh := mul_le_mul_of_nonneg_left (hφ i).1 (by positivity : (0:ℝ) ≤ C*n)
    have he : (C*n)*(1/(C*n))=1 := by field_simp
    rwa [he] at hh
  have hP : ∀ i, (P i).Nonempty := fun i => card_pos.mp (by rw [hcard]; norm_num)
  have hp : (0:ℝ) ≤ n^2 := sq_nonneg _
  have ha : 0 ≤ C*n := by positivity
  have hpD : n^2 ≤ n^2+C*n := le_add_of_nonneg_right ha
  have hdegree := multiplicity_degree_cap P φ (n^2) (C*n) hp ha hφ₀ hfloor hload
  have hcodegree : ∀ e f, e ≠ f →
      ((∑ i, if e ∈ P i ∧ f ∈ P i then seedMultiplicity (n^2) φ i else 0:ℕ):ℝ) ≤
        (n^2+C*n)^((3:ℝ)/4) := by
    intro e f hef
    have hh := multiplicity_codegree_cap P φ (n^2) (C/n) hp (by positivity) hφ₀
      (fun i => (hφ i).2) hlin e f hef
    have he : n^2*(C/n)+1=C*n+1 := by field_simp <;> ring
    rw [he] at hh
    exact hh.trans hcode
  have htotal := multiplicity_total_cap P φ (n^2) (C*n) hp ha hφ₀ hfloor hP hload
  have htotal' : ((∑ i, seedMultiplicity (n^2) φ i:ℕ):ℝ) ≤
      Real.exp ((n^2+C*n)^(((1:ℝ)/3200)^2)) :=
    htotal.trans ((mul_le_mul_of_nonneg_left hE (by positivity)).trans hsize)
  obtain ⟨Q,hQ,hWeights⟩ := hMatch (n^2+C*n) (n^2) (C*n) hD₀ hD1 hp hpD ha
    E ι P φ hcard hφ₀ hfloor hdegree (by norm_num at hcodegree ⊢; exact hcodegree)
      (by norm_num at htotal' ⊢; exact htotal') κ W (fun k i => (hW k i).1)
      (by norm_num at htests ⊢; exact hκ.trans htests)
  refine ⟨Q,hQ,?_⟩
  intro k
  have hS : 0 ≤ ∑ i, φ i*W k i := sum_nonneg fun i _ => mul_nonneg (hφ₀ i) (hW k i).1
  have hh := hWeights k (by
    intro i
    have hw := mul_le_mul_of_nonneg_right (hW k i).2
      (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ n^2+C*n) ((5:ℝ)/4))
    norm_num at hw ⊢
    exact hw.trans (hmasscap.trans (mul_le_mul_of_nonneg_left (hmass k) hp)))
  have hfac : (n^2+C*n)^(-((1:ℝ)/3200))*(n^2+C*n)/(n^2+C*n)+
      (n^2+C*n-n^2+C*n)/(n^2+C*n) ≤ η := by
    have hd : n^2+C*n ≠ 0 := by positivity
    convert herror using 1 <;> field_simp <;> ring
  norm_num at hh hfac
  exact hh.trans (mul_le_mul_of_nonneg_right hfac hS)
#print axioms matching_from_integer_multiplicities_explicit
#print axioms fractional_matching_of_caps_explicit
#print axioms diffuse_weighted_matching_explicit
end TypedTriangle.WeightedClone.Explicit
