module
public import RequestProject.TypedTriangle.PaschRawAmbientTuplePacking
public import RequestProject.TypedTriangle.PaschSampledTupleControl
public import RequestProject.TypedTriangle.PaschPackingSampling
public import RequestProject.TypedTriangle.RawHostStock
public import RequestProject.TypedTriangle.ReserveCommonNbr
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.BasalIncidence
open TypedTriangle.Pasch

/-- The actual residual-profile margin used before stock thinning. -/
def rawStockProfileMargin (α : ℝ) : ℝ := min (α/128) (1/16)

/-- Rich raw stock: the actual raw packing and sampled subfamily are both
returned. The raw packing carries all eligible tuple tests, and its sampled
subfamily inherits the nonnegative ambient upper bound. No relative
approximation after thinning or exact diffuse seed is asserted. -/
theorem reserve_from_raw_profile_with_pasch_ambient_and_tuple_tests {I : Type} (F : Set (Multiset I))
    (a b α ζ : ℝ) (h qTests : ℕ) (hζ : 0 < ζ) (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) :
    ∃ θ ε γ : ℝ, 0 < θ ∧ 0 < ε ∧ 0 < γ ∧
      ∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ,
        ∀ {V : Type} [Fintype V] (H : Host V I) (μ : Finset V → ℝ)
          (S B : Finset (Sym2 V)) (DS : Finset (Finset V)) (dS dB : ℕ),
          n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
          (∀ T, IsAllowed H F T → a/Fintype.card V ≤ μ T ∧ μ T ≤ b/Fintype.card V) →
          (∀ e ∈ edges H, |bdry H F μ e-1| ≤ ε) →
          S ⊆ edges H → IsDecomposition H F S DS → Disjoint S B →
          (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ θ*Fintype.card V →
          (∀ v, degIn B v ≤ dB) → (dB:ℝ) ≤ γ*Fintype.card V →
          ∀ (Z : Type) [Fintype Z] (e : V ↪ Z) (Rprev : Finset (Finset Z)) (Lprev : ℕ),
          PairCodegreeBound Rprev Lprev →
          ∀ (ν : Type) [Fintype ν] (X : ℕ → ν → Finset (Finset V) → ℝ),
          Fintype.card ν ≤ (Fintype.card V)^qTests →
          (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k U, 0 ≤ X ℓ k U) →
          ∃ Praw D : Finset (Finset V),
            CommonNbrCond (residual H (S∪B)) F (α/2) ∧
            (∀ f ∈ edges (residual H (S∪B)),
              |bdry (residual H (S∪B)) F μ f-1| ≤ rawStockProfileMargin α) ∧
            Praw ⊆ allowed (residual H (S∪B)) F ∧ IsPacking (residual H (S∪B)) F Praw ∧
            (Pasch.count Praw:ℝ) ≤ rawPaschPackingCost a b*(Fintype.card V:ℝ)^2 ∧
            D ⊆ Praw ∧ IsDecomposition H F (cover D) D ∧
            Disjoint (cover D) (S∪B) ∧
            (∀ v, (degIn (cover D) v:ℝ) < ρ*Fintype.card V) ∧
            (∀ u v, H.G.Adj u v → κ*Fintype.card V ≤ (good H F D u v).card) ∧
            (Pasch.count D:ℝ) ≤ δ*(Fintype.card V:ℝ)^2 ∧
            (∑ T ∈ D, childPaddedWeight e Rprev Lprev T) ≤ (1+ζ)*b*Fintype.card V ∧
            ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k : ν,
              floorTupleTestControl (allowed (residual H (S∪B)) F)
                (fun T => μ T/(1+rawStockProfileMargin α)) Praw (X ℓ k) ℓ := by
  have hb : 0 < b := ha.trans_le hab
  let r := rawStockProfileMargin α
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrα : r ≤ α/128 := min_le_left _ _
  have hrHalf : r ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  let θ := min (α/64) (r/(16*b))
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  let ε := r/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨NRaw,hRaw⟩ := raw_fractional_packing_with_pasch_ambient_and_tuple_tests
    a b (α/2) (α/32) ζ qTests ha hab (by positivity) (by positivity) hζ
  refine ⟨θ,ε,θ,hθ,hε,hθ,?_⟩
  intro ρ δ hρ hδ
  let K := rawPaschPackingCost a b
  have hK : 0 ≤ K := pow_nonneg
    (lt_of_lt_of_le zero_lt_one (rawProfileConstant_one_le a b)).le 3
  let q := PaschSampling.thinRate ρ K δ
  have hq : 0 < q := PaschSampling.thinRate_pos hρ hK hδ
  have hCaps := PaschSampling.thinRate_caps hρ hK hδ
  let κ := (α/2)*q^2/2
  refine ⟨κ,by dsimp [κ]; positivity,
    max 1 (max NRaw (PaschSampling.samplingOrder q (α/2))),?_⟩
  intro V _ H μ S B DS dS dB hn h3 h4 hμ hLoad hS hDS hSB hdS hdθ hdB hdγ
    Z _ e Rprev Lprev hPrev ν _ X hν hX
  have hnNat : 0 < Fintype.card V := by omega
  have hn0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast hnNat
  let R := S∪B
  let d := dS+dB
  let J := residual H R
  have hJE : edges J = edges H\R := Residual.edges_subHost_eq sdiff_subset
  have hDegree (v : V) : degIn R v ≤ d := by
    change ((S∪B).filter (fun e => v ∈ e)).card ≤ dS+dB
    rw [filter_union]
    exact (card_union_le _ _).trans (Nat.add_le_add (hdS v) (hdB v))
  have hdTwo : (d:ℝ) ≤ 2*θ*Fintype.card V := by
    dsimp only [d]
    push_cast
    linarith only [hdθ,hdγ]
  have hdα : (d:ℝ) ≤ α/32*Fintype.card V := by
    have hh := mul_le_mul_of_nonneg_right (show θ ≤ α/64 from min_le_left _ _) hn0.le
    linarith only [hdTwo,hh]
  have hCost : 2*b*d/(Fintype.card V:ℝ) ≤ r/4 := by
    apply (div_le_iff₀ hn0).mpr
    have hPay : θ*(16*b) ≤ r := (le_div_iff₀ (by positivity : 0 < 16*b)).mp (min_le_right _ _)
    have hPayN := mul_le_mul_of_nonneg_right hPay hn0.le
    have hD := mul_le_mul_of_nonneg_left hdTwo (by positivity : 0 ≤ 2*b)
    nlinarith only [hPayN,hD]
  have hMu0 : ∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b/Fintype.card V := by
    intro T hT
    exact ⟨(by positivity : (0:ℝ) ≤ a/Fintype.card V).trans (hμ T hT).1,(hμ T hT).2⟩
  have hDeleted := RawReference.load_after_deletion μ R d b ε hn0 hb.le hMu0 hDegree hLoad
  have hLoadJ : ∀ e ∈ edges J, |bdry J F μ e-1| ≤ r := by
    intro e he
    exact (hDeleted e he).trans (by dsimp only [ε]; linarith only [hCost,hr])
  have h3J := residual_commonNbrCond h3 R d hDegree
    (hdα.trans (mul_le_mul_of_nonneg_right (show α/32 ≤ α/4 by linarith only [hα]) hn0.le))
  obtain ⟨P,hPsub,hPJ,hNear,hCount,hRelative,hAmbientSub,hControls⟩ := hRaw J F μ r
    ((le_max_left _ _).trans ((le_max_right _ _).trans hn)) hr.le hrHalf
    (fun T hT => hμ T (isAllowed_mono (subHost_le H _) rfl hT)) hLoadJ h3J
      Z e Rprev Lprev hPrev ν X hν hX
  have hPH : IsPacking H F P := ⟨fun T hT =>
    isAllowed_mono (subHost_le H _) rfl (hPJ.1 T hT),hPJ.2⟩
  have hPE : cover P ⊆ edges J := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hPJ.1 T hT) heT
  have hAvoid : Disjoint (cover P) R := by
    rw [hJE] at hPE
    exact disjoint_left.mpr fun e he hR => (mem_sdiff.mp (hPE he)).2 hR
  have hMissing : ∀ v, (((edges H\cover P).filter (fun e => v ∈ e)).card:ℝ) ≤
      (α/4)*Fintype.card V := by
    intro v
    have hSplit : (edges H\cover P).filter (fun e => v ∈ e) ⊆
        (edges J\cover P).filter (fun e => v ∈ e) ∪ R.filter (fun e => v ∈ e) := by
      intro e he
      obtain ⟨he,hv⟩ := mem_filter.mp he
      by_cases heR : e ∈ R
      · exact mem_union_right _ (mem_filter.mpr ⟨heR,hv⟩)
      · apply mem_union_left
        apply mem_filter.mpr
        refine ⟨mem_sdiff.mpr ⟨?_,(mem_sdiff.mp he).2⟩,hv⟩
        rw [hJE]
        exact mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,heR⟩
    have hCard : (((edges H\cover P).filter (fun e => v ∈ e)).card:ℝ) ≤
        (((edges J\cover P).filter (fun e => v ∈ e)).card:ℝ)+(degIn R v:ℝ) := by
      exact_mod_cast (card_le_card hSplit).trans (card_union_le _ _)
    have hRdeg : (degIn R v:ℝ) ≤ d := by exact_mod_cast hDegree v
    have hRate := mul_le_mul_of_nonneg_right hrα hn0.le
    have hNearV : (((edges J\cover P).filter (fun e => v ∈ e)).card:ℝ) ≤
        (2*r+α/32)*Fintype.card V := by simpa only [cover] using hNear v
    have hαn : 0 ≤ α*(Fintype.card V:ℝ) := mul_nonneg hα.le hn0.le
    nlinarith only [hCard,hNearV,hRdeg,hdα,hRate,hαn]
  have hCover := CorePaid.edge_covered_of_approx μ
    (show ε < 1 by dsimp only [ε]; linarith only [hrHalf]) hLoad
  let A := {uv : V×V // H.G.Adj uv.1 uv.2}
  let u : A → V := fun t => t.val.1
  let v : A → V := fun t => t.val.2
  have hA : Fintype.card A ≤ Fintype.card V^2 := by
    calc
      Fintype.card A ≤ Fintype.card (V×V) := Fintype.card_subtype_le _
      _ = _ := by rw [Fintype.card_prod]; ring
  have hSupply : ∀ t : A, (α/2)*Fintype.card V ≤ (good H F P (u t) (v t)).card := by
    intro t
    obtain ⟨T,hT,heT⟩ := hCover s(u t,v t) (by simpa [SparseEdge.edges] using t.property)
    obtain ⟨w,hw⟩ := eq_insert_of_mem_triEdges hT.1 heT
    have hTa : IsAllowed H F {u t,v t,w} := by rwa [tri_eq_insert_toFinset,←hw]
    have hh := good_supply h3 P hMissing hTa
    nlinarith only [hh]
  obtain ⟨D,hDP,hD,hSmall,hGood,hPasch⟩ := PaschSampling.sample_packing_with_pasch
    q (α/2) K δ hq ((hCaps.2.1).trans (by norm_num)) (by positivity) hK hδ hCaps.2.2
      V I H F P hPH ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
        hCount A u v hA hSupply
  refine ⟨P,D,h3J,hLoadJ,hPsub,hPJ,hCount,hDP,hD,?_,?_,?_,hPasch,hAmbientSub D hDP,hControls⟩
  · apply hAvoid.mono_left
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨T,hDP hT,heT⟩
  · intro x
    have hh := hSmall x
    have hPay := mul_le_mul_of_nonneg_right hCaps.1 hn0.le
    have hPos := mul_pos hρ hn0
    change (((cover D).filter (fun e => x ∈ e)).card:ℝ) < ρ*Fintype.card V
    nlinarith only [hh,hPay,hPos]
  · intro x y hxy
    have hh := hGood ⟨(x,y),hxy⟩
    dsimp only [u,v] at hh
    change κ*Fintype.card V ≤ _
    dsimp only [κ]
    nlinarith only [hh]

#print axioms reserve_from_raw_profile_with_pasch_ambient_and_tuple_tests
end TypedTriangle.BasalIncidence
