module
public import RequestProject.TypedTriangle.ExplicitSeedPersistence
public import RequestProject.TypedTriangle.ExplicitMonitoredPackingCore
public import RequestProject.TypedTriangle.G3BasalRemainderSplit
public import RequestProject.TypedTriangle.G4SelectorSameResidue
public import RequestProject.TypedTriangle.ActualResidualCharge
public import RequestProject.TypedTriangle.SeedMoment
public import RequestProject.TypedTriangle.TriangleMonitorSeedComparison
public import RequestProject.TypedTriangle.TriangleMonitorStockTransition
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


namespace TypedTriangle.ExplicitSeed
variable {V I : Type*} [Fintype V]

def seedPointwiseCost (α C : ℝ) (h : ℕ) : ℝ := (16*C+4)*provL α (2*C) h
def seedExactBudget (C α : ℝ) (h : ℕ) : ℝ := RawReference.Explicit.seedBudget (1/C) C α h
def seedExactOrder (C : ℝ) : ℕ := RawReference.Explicit.seedOrder C

theorem seedPointwiseCost_nonneg (h : ℕ) {α C : ℝ} (hα : 0 < α) (hC : 0 < C) :
    0 ≤ seedPointwiseCost α C h :=
  mul_nonneg (by positivity) (provL_nonneg hα (by positivity) h)


theorem seed_persistence_approx_with_pointwise_bound_explicit {F : Set (Multiset I)} {a b α : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hα : 0 < α) (hh : ℕ) :
    ∀ {W : Type*} [Fintype W] (H : Host W I) (μ : Finset W → ℝ)
      (B : Finset (Sym2 W)) (Q : Finset (Finset W)) (d : ℕ) (e : ℝ),
      RawReference.Explicit.seedOrder b ≤ Fintype.card W → HingeCond H F α hh →
      (∀ T, IsAllowed H F T → a / Fintype.card W ≤ μ T ∧ μ T ≤ b / Fintype.card W) →
      0 ≤ e → e ≤ 1 / 2 → (∀ f ∈ edges H, |bdry H F μ f - 1| ≤ e) →
      B ⊆ edges H → IsDecomposition H F B Q → (∀ x, degIn B x ≤ d) →
      (d : ℝ) ≤ RawReference.Explicit.seedBudget a b α hh * Fintype.card W →
      ∃ ψ : Finset W → ℝ, (∀ S, ψ S ≠ 0 → IsAllowed (residual H B) F S) ∧
        (∀ S, IsAllowed (residual H B) F S →
          a / (2 * Fintype.card W) ≤ ψ S ∧ ψ S ≤ (b + a / 2) / Fintype.card W) ∧
        (∀ f ∈ edges H, f ∉ B →
          |bdry (residual H B) F ψ f - 1| ≤ (1 + 2 * d * (4 * b / Fintype.card W)) * e) ∧
        (∀ S, IsAllowed (residual H B) F S →
          |ψ S - μ S| ≤ (16*b+4)*provL α (2*b) hh*d / (Fintype.card W:ℝ)^2) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set κ₀ := 2 * b
  set L := provL α κ₀ hh
  have hL0 : 0 ≤ L := provL_nonneg hα (by positivity) hh
  intro W _ H μ B Q d e hn0 hcond hμ he0 he1 hload hB hQ hdeg hd
  have hn0' : ((⌈16 * b⌉₊ : ℕ) : ℝ) + 1 ≤ (Fintype.card W : ℝ) := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ Fintype.card W := by
    have : (1 : ℕ) ≤ Fintype.card W := by
      change ⌈16*b⌉₊+1 ≤ Fintype.card W at hn0
      omega
    exact_mod_cast this
  set n := (Fintype.card W : ℝ)
  have hn16 : 16 * b < n := by linarith [Nat.le_ceil (16 * b)]
  have hn : 0 < n := by linarith
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hdε1 : (d : ℝ) ≤ α / (10 * 2 ^ Nat.choose hh 2) * n :=
    hd.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn.le)
  have hdε2 : (d : ℝ) ≤ 1 / (32 * b) * n :=
    hd.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hn.le)
  have hdε3 : (d : ℝ) ≤ a / (2 * (16 * b + 4) * (L + 1)) * n :=
    hd.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hn.le)
  -- ventanas del proveedor
  have hd1 : 10 * 2 ^ Nat.choose hh 2 * (d : ℝ) ≤ α * n := by
    have h2 : (0 : ℝ) < 10 * 2 ^ Nat.choose hh 2 := by positivity
    have := mul_le_mul_of_nonneg_left hdε1 h2.le
    rw [show 10 * 2 ^ Nat.choose hh 2 * (α / (10 * 2 ^ Nat.choose hh 2) * n) = α * n by
      field_simp] at this
    exact this
  have hd2 : 8 * κ₀ * d + 4 * κ₀ ≤ n := by
    have := mul_le_mul_of_nonneg_left hdε2 (by positivity : (0 : ℝ) ≤ 16 * b)
    rw [show 16 * b * (1 / (32 * b) * n) = n / 2 by field_simp; ring] at this
    simp only [κ₀]; nlinarith
  -- grado triangular desde las cargas
  have hμ0 : ∀ T ∈ allowed H F, 0 ≤ μ T := fun T hT =>
    le_trans (by positivity) (hμ T (by simpa [allowed] using hT)).1
  have hμb : ∀ T ∈ allowed H F, μ T ≤ b / n := fun T hT => (hμ T (by simpa [allowed] using hT)).2
  have htri : ∀ f ∈ edges H, n ≤ κ₀ * (triOn H F f).card := by
    intro f hf
    have h1 := hload f hf
    rw [abs_le] at h1
    have h2 : bdry H F μ f ≤ (triOn H F f).card * (b / n) := by
      rw [bdry_eq_sum_triOn]
      calc ∑ T ∈ triOn H F f, μ T ≤ ∑ _T ∈ triOn H F f, b / n :=
            sum_le_sum fun T hT => hμb T (mem_filter.1 hT).1
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    have h3 : (1 : ℝ) / 2 ≤ (triOn H F f).card * (b / n) := by linarith
    rw [mul_div_assoc', le_div_iff₀ hn] at h3
    simp only [κ₀]; nlinarith
  obtain ⟨hK, hD⟩ := provK_hyp_disp (by positivity) (by positivity) hcond htri hB hdeg hd1 hd2
  set K := provK H F B α hh
  set cert := kcert H F B K
  set p := pivB K B
  have hcert : ∀ T ∈ allowed H F, ∀ f, bdry H F (cert T) f =
      indR (triEdges T) f - pivotTermW H F B p T f := by
    intro T hT f
    rw [pivotTermW_pivB]
    exact bdry_kcert hK (by simpa [allowed] using hT) f
  have hsupp : ∀ T ∈ allowed H F, ∀ S, cert T S ≠ 0 → IsAllowed (residual H B) F S :=
    fun T hT S hS => kcert_support hK (by simpa [allowed] using hT) hS
  have hψsupp := transported_support (μ := μ) hQ cert hsupp
  refine ⟨transported H F μ Q cert, hψsupp, ?_, ?_, ?_⟩
  · -- positividad
    intro S hS
    obtain ⟨hSA, hSB⟩ := residual_allowed hS
    have hSa : S ∈ allowed H F := by simpa [allowed] using hSA
    have hδ : ∀ T ∈ allowed H F, Disjoint (triEdges T) B → ∀ S,
        cert T S = if S = T then 1 else 0 := fun T _ hT S => kcert_delta hT S
    have hLc : ∀ T ∈ allowed H F, ¬ Disjoint (triEdges T) B → ∀ S,
        |cert T S| ≤ L * ptw S (1 / Fintype.card W) T := by
      intro T hT hTB S
      have := kcert_hL (by positivity : (0 : ℝ) < α / 2) (by positivity : (0 : ℝ) ≤ 2 * κ₀)
        hK hD hn1 (by simpa [allowed] using hT) hTB S
      exact this
    have hsmall : (16 * b + 4) * L * 1 ^ 3 * d / n ^ 2 ≤ a / (2 * n) := by
      rw [one_pow, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : (16 * b + 4) * L * d ≤ (16 * b + 4) * (L + 1) * d := by
        have : (16 * b + 4) * L * d ≤ (16 * b + 4) * L * d + (16 * b + 4) * d := by
          nlinarith
        nlinarith
      have h2 : (16 * b + 4) * (L + 1) * d ≤ a * n / 2 := by
        have hpos : (0 : ℝ) < 2 * (16 * b + 4) * (L + 1) := by positivity
        have := mul_le_mul_of_nonneg_left hdε3 hpos.le
        rw [show 2 * (16 * b + 4) * (L + 1) * (a / (2 * (16 * b + 4) * (L + 1)) * n) = a * n by
          field_simp] at this
        nlinarith
      nlinarith
    exact seed_positivity hB hQ hdeg hμ0 hμb cert hL0 le_rfl hn1 hδ hLc hsmall hSa hSB
      (hμ S hSA).1
  · -- cargas
    intro f hf hfB
    have hres := bdry_residual_eq (H := H) (F := F) (Fst := B) _ hψsupp f
    rw [hres]
    have hp0 : ∀ g T, 0 ≤ p g T := by
      intro g T; unfold p pivB; split_ifs
      · exact pivK_nonneg K g T
      · exact le_rfl
    have hpκ : ∀ g T, p g T ≤ (4 * b) / n := by
      intro g T
      unfold p pivB
      split_ifs with hg
      · refine (pivK_le (hK.piv_ne g hg) (fun c hc => (hK.piv_ok g hg c hc).2.1) T).trans ?_
        have hsz := hD.piv_size g hg
        have hP0 : (0 : ℝ) < (K.Piv g).card := by exact_mod_cast card_pos.2 (hK.piv_ne g hg)
        rw [div_le_div_iff₀ hP0 hn]
        simp only [κ₀] at hsz; nlinarith
      · positivity
    have hpsupp : ∀ g T, p g T ≠ 0 → g ∈ triEdges T := by
      intro g T hT
      unfold p pivB at hT
      split_ifs at hT with hg
      · obtain ⟨c, hc, hc0⟩ := exists_ne_zero_of_avgOver_ne_zero hT
        have hTc : T = insert c g.toFinset := by by_contra hne; exact hc0 (if_neg hne)
        have hgnd : ¬ g.IsDiag := by
          have := hB hg
          simp only [edges, mem_filter, mem_univ, true_and] at this
          exact H.G.not_isDiag_of_mem_edgeSet this
        rw [hTc]
        exact mem_triEdges_of_toFinset_subset hgnd (subset_insert _ _)
      · exact absurd rfl hT
    have hr : ∀ g ∈ edges H, |(bdry H F μ g - 1)| ≤ e := hload
    have := transport_error_avg_local (r := fun g => bdry H F μ g - 1)
      (fun g _ => by ring) hr hQ hB hdeg p hp0 hpκ hpsupp cert hcert hf hfB
    exact this

  · intro S hS
    obtain ⟨hSA,hSB⟩ := residual_allowed hS
    have hSa : S ∈ allowed H F := by simpa [allowed] using hSA
    have hδ : ∀ T ∈ allowed H F, Disjoint (triEdges T) B → ∀ S,
        cert T S = if S = T then 1 else 0 := fun T _ hT S => kcert_delta hT S
    have hLc : ∀ T ∈ allowed H F, ¬ Disjoint (triEdges T) B → ∀ S,
        |cert T S| ≤ L * ptw S (1 / Fintype.card W) T := by
      intro T hT hTB S
      exact kcert_hL (by positivity : (0:ℝ)<α/2) (by positivity : (0:ℝ)≤2*κ₀)
        hK hD hn1 (by simpa [allowed] using hT) hTB S
    have hp := seed_perturbation_scaled hB hQ hdeg hμ0 hμb cert hL0
      (le_refl (1:ℝ)) hn1 hδ hLc hSa hSB
    simpa only [one_pow,mul_one] using hp

theorem seed_persistence_exact_with_pointwise_bound_explicit {F : Set (Multiset I)} {C α : ℝ} (hC : 1 ≤ C) (hα : 0 < α)
    (hh : ℕ) :
    ∀ {W : Type*} [Fintype W] (H : Host W I) (φ : Finset W → ℝ)
      (B : Finset (Sym2 W)) (Q : Finset (Finset W)) (d : ℕ),
      seedExactOrder C ≤ Fintype.card W → IsDiffuseSeed H F C φ → HingeCond H F α hh →
      B ⊆ edges H → IsDecomposition H F B Q → (∀ x, degIn B x ≤ d) →
      (d : ℝ) ≤ seedExactBudget C α hh * Fintype.card W →
      ∃ ψ : Finset W → ℝ, IsDiffuseSeed (residual H B) F (2 * C) ψ ∧
        (∀ S, ψ S ≠ 0 → IsAllowed (residual H B) F S) ∧
        (∀ S, IsAllowed (residual H B) F S →
          |ψ S - φ S| ≤ seedPointwiseCost α C hh*d / (Fintype.card W:ℝ)^2) := by
  have hC0 : 0 < C := by linarith
  intro W _ H φ B Q d hn0 hφ hcond hB hQ hdeg hd
  have hμ : ∀ T, IsAllowed H F T →
      1 / C / Fintype.card W ≤ φ T ∧ φ T ≤ C / Fintype.card W := by
    intro T hT
    obtain ⟨h1, h2⟩ := hφ.1 T hT
    refine ⟨?_, h2⟩
    rwa [div_div]
  have hload : ∀ f ∈ edges H, |bdry H F φ f - 1| ≤ 0 := by
    intro f hf
    have hfe : f ∈ H.G.edgeSet := by simpa [edges] using hf
    rw [bdry_eq_sum_triOn]
    unfold triOn
    rw [hφ.2 f hfe, sub_self, abs_zero]
  obtain ⟨ψ, hsupp, hpos, hld, hclose⟩ :=
    seed_persistence_approx_with_pointwise_bound_explicit (F := F) (a := 1/C) (b := C)
      (by positivity) (by rw [div_le_iff₀ hC0]; nlinarith) hα hh
      H φ B Q d 0 hn0 hcond hμ le_rfl (by norm_num) hload hB hQ hdeg hd
  refine ⟨ψ, ⟨fun T hT => ?_, fun f hf => ?_⟩, hsupp, hclose⟩
  · obtain ⟨h1, h2⟩ := hpos T hT
    have hn : (0 : ℝ) < Fintype.card W := by
      have := hT.1
      have : 0 < Fintype.card W := Fintype.card_pos_iff.2 ⟨Classical.choice
        (by obtain ⟨x, -⟩ := card_pos.1 (by omega : 0 < T.card); exact ⟨x⟩)⟩
      exact_mod_cast this
    constructor
    · refine le_trans (le_of_eq ?_) h1
      field_simp
    · refine h2.trans ?_
      rw [div_le_div_iff_of_pos_right hn]
      have : 1 / C / 2 ≤ C := by
        rw [div_div, div_le_iff₀ (by positivity)]; nlinarith
      linarith
  · have hfe : f ∈ edges H ∧ f ∉ B := by
      simp only [residual, subHost, SimpleGraph.edgeSet_inf, SimpleGraph.edgeSet_fromEdgeSet,
        Set.mem_inter_iff, Set.mem_diff, coe_sdiff, mem_coe] at hf
      exact ⟨hf.1.1.1, hf.1.1.2⟩
    have := hld f hfe.1 hfe.2
    rw [mul_zero, abs_nonpos_iff, sub_eq_zero] at this
    rw [← this, bdry_eq_sum_triOn]
    rfl


#print axioms seed_persistence_approx_with_pointwise_bound_explicit
#print axioms seed_persistence_exact_with_pointwise_bound_explicit
end TypedTriangle.ExplicitSeed


namespace TypedTriangle.TriangleMonitors.Explicit
alias edge_card_le_of_degree_bound := TypedTriangle.TriangleMonitors.edge_card_le_of_degree_bound
alias original_complement_degree := TypedTriangle.TriangleMonitors.original_complement_degree
alias removed_seed_mass_le := TypedTriangle.TriangleMonitors.removed_seed_mass_le
alias triangle_seed_statistic_comparison := TypedTriangle.TriangleMonitors.triangle_seed_statistic_comparison
#print axioms removed_seed_mass_le
#print axioms triangle_seed_statistic_comparison
end TypedTriangle.TriangleMonitors.Explicit


namespace TypedTriangle.WeightedStar.Explicit
open LocalizedCover

def jointTrianglePackingOrder (C α η τ L : ℝ) (q : ℕ) : ℕ :=
  localizedSignedOrder C α η τ (L+1) q


/-- A single actual nibble controls the edge moments needed by the bank and
arbitrary bounded triangle statistics. No lower mass assumption is imposed on
an individual triangle monitor. All three families share the same packing. -/
theorem joint_sparse_packing_with_triangle_monitors_explicit (C α η τ L : ℝ) (q : ℕ)
    (hC : 0 < C) (hα : 0 < α) (hη : 0 < η) (hτ : 0 < τ) (hL : 0 < L) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), jointTrianglePackingOrder C α η τ L q ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      CommonNbrCond H F α → ∀ (κ ι ν : Type) [Fintype κ] [Fintype ι] [Fintype ν]
      (bad : κ → Finset V) (loc : κ → Sym2 V → ℝ) (full : ι → Sym2 V → ℝ)
      (w : ν → Finset V → ℝ),
      ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*L*(T∩bad k).card) →
      (∀ k T, IsAllowed H F T → |triSum (full k) T| ≤ 3*L*T.card) →
      (∀ k T, IsAllowed H F T → |w k T| ≤ 1) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        (∀ k, |edgeSum (loc k) (edges H\P.biUnion triEdges)| ≤ τ*Fintype.card V*(bad k).card) ∧
        (∀ k, |edgeSum (full k) (edges H\P.biUnion triEdges)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
        ∀ k, |(∑ T ∈ P, w k T)-(∑ T ∈ allowed H F, φ T*w k T)| ≤
          τ*(Fintype.card V:ℝ)^2 := by
  intro V I _ H F φ hn hφ h3 κ ι ν _ _ _ bad loc full w hcard hloc hfull hw
  let bad' : κ ⊕ (ι ⊕ ν) → Finset V := Sum.elim bad (fun _ => univ)
  let wt : κ ⊕ (ι ⊕ ν) → Finset V → ℝ :=
    Sum.elim (fun k T => triSum (loc k) T)
      (Sum.elim (fun k T => triSum (full k) T) w)
  have hcard' : (Fintype.card (κ ⊕ (ι ⊕ ν)):ℝ) ≤ (Fintype.card V:ℝ)^q := by
    simpa only [Fintype.card_sum,Nat.add_assoc] using hcard
  have hEnvelope : ∀ k T, IsAllowed H F T →
      |wt k T| ≤ 3*(L+1)*(T∩bad' k).card := by
    intro k T hT
    rcases k with k | (k | k)
    · exact (hloc k T hT).trans (by
        dsimp only [bad',Sum.elim_inl]
        have hc : (0:ℝ) ≤ (T∩bad k).card := Nat.cast_nonneg _
        nlinarith only [hc])
    · simpa only [wt,Sum.elim_inr,Sum.elim_inl,bad',inter_univ] using
        (hfull k T hT).trans (by
          have hc : (0:ℝ) ≤ T.card := Nat.cast_nonneg _
          nlinarith only [hc])
    · dsimp only [wt,Sum.elim_inr,bad']
      rw [inter_univ,hT.1]
      exact (hw k T hT).trans (by norm_num; linarith)
  obtain ⟨P,hPsub,hP,hSparse,hQuota⟩ :=
    localized_signed_packing_of_H1H3_explicit C α η τ (L+1) q
      hC hα hη hτ (by positivity) H F φ hn hφ h3 (κ ⊕ (ι ⊕ ν)) bad' wt hcard' hEnvelope
  have hPE : P.biUnion triEdges ⊆ edges H := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  refine ⟨P,hPsub,hP,hSparse,?_,?_,?_⟩
  · intro k
    exact remainder_moment_of_quota hφ P hP hPE (loc k)
      (τ*Fintype.card V*(bad k).card) (hQuota (.inl k))
  · intro k
    have hh := remainder_moment_of_quota hφ P hP hPE (full k)
      (τ*Fintype.card V*(univ : Finset V).card) (hQuota (.inr (.inl k)))
    simpa only [card_univ,pow_two,mul_assoc] using hh
  · intro k
    have hh := hQuota (.inr (.inr k))
    simpa only [wt,Sum.elim_inr,bad',card_univ,pow_two,mul_assoc] using hh

#print axioms joint_sparse_packing_with_triangle_monitors_explicit
end TypedTriangle.WeightedStar.Explicit


namespace TypedTriangle.StockEntry.Explicit
alias monitored_stock_transition_retaining_initial_packing_explicit :=
  TypedTriangle.StockEntry.monitored_stock_transition_retaining_initial_packing
#print axioms monitored_stock_transition_retaining_initial_packing_explicit
end TypedTriangle.StockEntry.Explicit


namespace TypedTriangle.StockEntry.Explicit
open BasalIncidence ProtectedNibble LocalizedCover

def triangleStockOrder (C α κ η τ L : ℝ) (_h qMon : ℕ) : ℕ :=
  let εc := coverDownBudget κ η
  let δ := min (εc/4) (min (1/4) η)
  max (WeightedStar.Explicit.jointTrianglePackingOrder C α δ τ L qMon)
    (max (coverDownOrder κ η) ⌈2/εc⌉₊)


theorem g4_nibble_after_stock_deletion_with_triangle_monitors_explicit {I : Type} (F : Set (Multiset I))
    (C α κ η τ L : ℝ) (h qMon : ℕ) (hC : 1 ≤ C) (hα : 0 < α)
    (hκ : 0 < κ) (hη : 0 < η) (hτ : 0 < τ) (hL : 0 < L) :
    ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (D DR : Finset (Finset V)) (R : Finset (Sym2 V)),
        triangleStockOrder C α κ η τ L h qMon ≤ Fintype.card V →
        let S := cover D∪R
        let J := subHost H (edges H\S)
        IsDiffuseSeed J F C φ → IsPhysical J F (edges J) →
        CommonNbrCond J F α → HingeCond J F α h →
        IsPhysical H F (edges H) →
        IsDecomposition H F (cover D) D → IsDecomposition H F R DR →
        Disjoint (cover D) R →
        (∀ u v, H.G.Adj u v → κ*Fintype.card V ≤ (good H F D u v).card) →
        ∀ (κi ι ν : Type) [Fintype κi] [Fintype ι] [Fintype ν]
          (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
          (full : ι → Sym2 V → ℝ) (w : ν → Finset V → ℝ),
          ((Fintype.card κi+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^qMon →
          (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤
            3*L*(T∩bad k).card) →
          (∀ j T, IsAllowed H F T → |triSum (full j) T| ≤ 3*L*T.card) →
          (∀ k T, IsAllowed H F T → |w k T| ≤ 1) →
          ∃ P₀ Q : Finset (Finset V), P₀ ⊆ Q ∧ IsPacking H F P₀ ∧
            (∀ T ∈ P₀, IsAllowed J F T) ∧
            (∀ v, (((edges J\P₀.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
            (∀ k, |(∑ T ∈ P₀, w k T)-(∑ T ∈ allowed J F, φ T*w k T)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
            IsPacking H F Q ∧
            Disjoint (Q.biUnion triEdges) R ∧
            (edges H\(R∪Q.biUnion triEdges)) ⊆ cover D ∧
            IsPhysical H F (edges H\(R∪Q.biUnion triEdges)) ∧
            ∃ d q : ℕ, ((2*d+2*q:ℕ):ℝ) ≤ η*Fintype.card V ∧
              (∀ k, |edgeSum (loc k) (edges H\(R∪Q.biUnion triEdges))-
                  edgeSum (loc k) (cover D)| ≤
                τ*Fintype.card V*(bad k).card+
                  (3*L*(bad k).card)*(2*d+2*q:ℕ)/2) ∧
              ∀ j, |edgeSum (full j) (edges H\(R∪Q.biUnion triEdges))-
                  edgeSum (full j) (cover D)| ≤
                τ*(Fintype.card V:ℝ)^2+
                  (3*L*Fintype.card V)*(2*d+2*q:ℕ)/2 := by
  let εc := coverDownBudget κ η
  have hεc : 0 < εc := coverDownBudget_pos hκ hη
  let nW := coverDownOrder κ η
  let δ := min (εc/4) (min (1/4) η)
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by norm_num) hη)
  let nP := WeightedStar.Explicit.jointTrianglePackingOrder C α δ τ L qMon
  intro V _ H φ D DR R hn
  change max nP (max nW ⌈2/εc⌉₊) ≤ Fintype.card V at hn
  dsimp only
  intro hSeed hPhysJ h3 h4 hPhysH hD hR hXR hSupply
    κi ι ν _ _ _ bad loc full w hcount hloc hfull hw
  let S := cover D∪R
  let J := subHost H (edges H\S)
  have hEmptyDec : IsDecomposition J F ∅ (∅ : Finset (Finset V)) := by
    simp [IsDecomposition]
  have hAllowLoc : ∀ k T, IsAllowed J F T →
      |triSum (loc k) T| ≤ 3*L*(T∩bad k).card := by
    intro k T hT
    exact hloc k T (isAllowed_mono (subHost_le H _) rfl hT)
  have hAllowFull : ∀ j T, IsAllowed J F T →
      |triSum (full j) T| ≤ 3*L*T.card := by
    intro j T hT
    exact hfull j T (isAllowed_mono (subHost_le H _) rfl hT)
  have hnP : nP ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hAllowW : ∀ k T, IsAllowed J F T → |w k T| ≤ 1 :=
    fun k T hT => hw k T (isAllowed_mono (subHost_le H _) rfl hT)
  obtain ⟨P,hPsub,hPJ,hSparse,hLocal,hGlobal,hTriangles⟩ :=
    WeightedStar.Explicit.joint_sparse_packing_with_triangle_monitors_explicit C α δ τ L qMon
      (by linarith) hα hδ hτ hL J F φ hnP hSeed h3 κi ι ν bad loc full w hcount hAllowLoc hAllowFull hAllowW
  have hPH : IsPacking H F P :=
    ⟨fun T hT => isAllowed_mono (subHost_le H _) rfl (hPJ.1 T hT),hPJ.2⟩
  have hPE : P.biUnion triEdges ⊆ edges J := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hPJ.1 T hT) heT
  have hPDis : Disjoint (P.biUnion triEdges) S := by
    apply disjoint_left.mpr
    intro e heP heS
    have hh : e ∈ edges H\S := by
      rw [←Residual.edges_subHost_eq (sdiff_subset : edges H\S ⊆ edges H)]
      exact hPE heP
    exact (mem_sdiff.mp hh).2 heS
  let U := edges J\P.biUnion triEdges
  let d := ⌈δ*Fintype.card V⌉₊
  have hdU : ∀ v, (U.filter (fun e => v ∈ e)).card ≤ d := by
    intro v
    have hv : ((edges J\P.biUnion triEdges).filter
        (fun e => v ∈ e)).card ≤ d := by
      exact_mod_cast (hSparse v).trans (Nat.le_ceil _)
    simpa only [U, sdiff_empty] using hv
  have hnε : 2 ≤ εc*Fintype.card V := by
    have h1 : 2/εc ≤ (Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hn))
    have hh := (div_le_iff₀ hεc).mp h1
    nlinarith
  have hdε : (d:ℝ) ≤ εc*Fintype.card V := by
    have hc : (d:ℝ) < δ*Fintype.card V+1 := Nat.ceil_lt_add_one (by positivity)
    have hδc : δ ≤ εc/4 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hδc (by positivity : (0:ℝ) ≤ Fintype.card V)]
  have hdiag : ∀ e ∈ U, ¬e.IsDiag := by
    intro e he
    have heJ : e ∈ edges J := (mem_sdiff.mp he).1
    have heH : e ∈ edges H := (mem_sdiff.mp (by
      simpa only [J, Residual.edges_subHost_eq sdiff_subset] using heJ :
        e ∈ edges H\S)).1
    exact H.G.not_isDiag_of_mem_edgeSet (by simpa [edges] using heH)
  have hm := Envelope.two_card_le_card_mul_degree U hdiag hdU
  let q := coverDownQuota κ η (Fintype.card V)
  obtain ⟨hwin,hqdeg⟩ := cover_down_window_explicit κ η hκ hη (Fintype.card V) U.card d
    ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
    (by omega) hdε
  have hJE : edges J = edges H\S := Residual.edges_subHost_eq sdiff_subset
  obtain ⟨Q,hPQ,hQ,hQR,hrem,hQphys,hMom⟩ :=
    monitored_stock_transition_retaining_initial_packing_explicit H F D DR P R hD hR hXR hPhysH
      hPH hPDis hSupply d q
      (by simpa only [S,J,U,hJE] using hdU)
      (by simpa only [S,J,U,hJE] using hwin)
  refine ⟨P,Q,hPQ,hPH,hPJ.1,?_,hTriangles,hQ,hQR,hrem,hQphys,d,q,hqdeg,?_,?_⟩
  · intro v
    exact (hSparse v).trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) (Nat.cast_nonneg _))
  · intro k
    exact hMom (loc k) (bad k) L (τ*Fintype.card V*(bad k).card)
      hL.le (hloc k) (by simpa only [S,J,hJE] using hLocal k)
  · intro k
    have htri : ∀ T, IsAllowed H F T →
        |triSum (full k) T| ≤ 3*L*(T∩(univ : Finset V)).card := by
      intro T hT
      simpa only [inter_univ] using hfull k T hT
    simpa only [card_univ] using hMom (full k) (univ : Finset V) L
      (τ*(Fintype.card V:ℝ)^2) hL.le htri
      (by simpa only [S,J,hJE] using hGlobal k)

#print axioms g4_nibble_after_stock_deletion_with_triangle_monitors_explicit
end TypedTriangle.StockEntry.Explicit


namespace TypedTriangle.CatalogNative.Explicit

open BasalIncidence StockEntry ProtectedNibble LocalizedCover

theorem nibble_after_basal_remainder_split_with_triangle_monitors_explicit {I : Type}
    (F : Set (Multiset I)) (C α κ η τ L : ℝ) (h qMon : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hκ : 0 < κ)
    (hη : 0 < η) (hτ : 0 < τ) (hL : 0 < L) :
    ∀ {V : Type} [Fintype V] (H : Host V I) (ψ : Finset V → ℝ)
        (D DT : Finset (Finset V))
        (R T Bank E : Finset (Sym2 V)),
        StockEntry.Explicit.triangleStockOrder C α κ η τ L h qMon ≤ Fintype.card V →
        let B := (((cover D ∪ R) ∪ T) ∪ Bank) ∪ E
        let J := subHost H (edges H \ B)
        IsDiffuseSeed J F C ψ → IsPhysical J F (edges J) →
        CommonNbrCond J F α → HingeCond J F α h →
        IsPhysical H F (edges H) →
        IsDecomposition H F (cover D) D →
        Basal H F R → IsDecomposition H F T DT →
        Basal H F Bank → Basal H F E →
        Disjoint (cover D) T →
        Disjoint R (cover D ∪ T) →
        Disjoint Bank ((cover D ∪ R) ∪ T) →
        Disjoint E (((cover D ∪ R) ∪ T) ∪ Bank) →
        (∀ u v, H.G.Adj u v →
          κ * Fintype.card V ≤ (good H F D u v).card) →
        ∀ (κi ι ν : Type) [Fintype κi] [Fintype ι] [Fintype ν]
          (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
          (full : ι → Sym2 V → ℝ) (w : ν → Finset V → ℝ),
          ((Fintype.card κi + Fintype.card ι + Fintype.card ν : ℕ) : ℝ) ≤
            (Fintype.card V : ℝ) ^ qMon →
          (∀ k A, IsAllowed H F A →
            |triSum (loc k) A| ≤ 3 * L * (A ∩ bad k).card) →
          (∀ j A, IsAllowed H F A →
            |triSum (full j) A| ≤ 3 * L * A.card) →
          (∀ k A, IsAllowed H F A → |w k A| ≤ 1) →
          ∃ (P₀ DR Q : Finset (Finset V)) (Rtail : Finset (Sym2 V)),
            P₀ ⊆ Q ∧ IsPacking H F P₀ ∧
            (∀ T ∈ P₀, IsAllowed J F T) ∧
            (∀ v, (((edges J\P₀.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
            (∀ k, |(∑ T ∈ P₀, w k T)-(∑ T ∈ allowed J F, ψ T*w k T)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
            IsDecomposition H F Rtail DR ∧
            Disjoint (cover D) Rtail ∧
            cover D ∪ Rtail = B ∧
            IsPacking H F Q ∧
            Disjoint (Q.biUnion triEdges) Rtail ∧
            (edges H \ (Rtail ∪ Q.biUnion triEdges)) ⊆ cover D ∧
            IsPhysical H F (edges H \ (Rtail ∪ Q.biUnion triEdges)) ∧
            ∃ d q : ℕ, ((2*d + 2*q : ℕ) : ℝ) ≤ η * Fintype.card V ∧
              (∀ k, |edgeSum (loc k)
                  (edges H \ (Rtail ∪ Q.biUnion triEdges)) -
                  edgeSum (loc k) (cover D)| ≤
                τ * Fintype.card V * (bad k).card +
                  (3 * L * (bad k).card) * (2*d + 2*q : ℕ) / 2) ∧
              ∀ j, |edgeSum (full j)
                  (edges H \ (Rtail ∪ Q.biUnion triEdges)) -
                  edgeSum (full j) (cover D)| ≤
                τ * (Fintype.card V : ℝ)^2 +
                  (3 * L * Fintype.card V) * (2*d + 2*q : ℕ) / 2 := by
  intro V _ H ψ D DT R T Bank E hn
  dsimp only
  intro hSeed hPhysJ h3 h4 hPhysH hD hR hT hBank hE
    hDT hRDT hBankDis hEDis hSupply κi ι ν _ _ _ bad loc full w
    hCount hLoc hFull hw
  obtain ⟨DR,hDR,hDtail,hEq⟩ :=
    basal_remainder_split D DT R T Bank E hR hT hBank hE
      hDT hRDT hBankDis hEDis
  obtain ⟨P₀,Q,hPQ,hP₀,hAllowed,hSparse,hQuota,hQ,hQR,hRem,hRemPhys,d,q,hLoad,hLocOut,hFullOut⟩ :=
    StockEntry.Explicit.g4_nibble_after_stock_deletion_with_triangle_monitors_explicit F C α κ η τ L h qMon
      hC hα hκ hη hτ hL H ψ D DR (((R ∪ T) ∪ Bank) ∪ E) hn
      (by simpa only [hEq] using hSeed)
      (by simpa only [hEq] using hPhysJ)
      (by simpa only [hEq] using h3)
      (by simpa only [hEq] using h4)
      hPhysH hD hDR hDtail hSupply
      κi ι ν bad loc full w hCount hLoc hFull hw
  refine ⟨P₀,DR,Q,((R ∪ T) ∪ Bank) ∪ E,hPQ,hP₀,?_,?_,?_,hDR,hDtail,hEq,
    hQ,hQR,hRem,hRemPhys,d,q,hLoad,hLocOut,hFullOut⟩

  · simpa only [hEq] using hAllowed
  · simpa only [hEq] using hSparse
  · simpa only [hEq] using hQuota

#print axioms nibble_after_basal_remainder_split_with_triangle_monitors_explicit

end TypedTriangle.CatalogNative.Explicit


namespace TypedTriangle.Vortex.Explicit
open CatalogNative StockEntry BasalIncidence S07V42 TypedTriangle.LocalizedCover

def triangleFixedPackingOrder (C α κ η τ Λ : ℝ) (h qMon : ℕ) : ℕ :=
  StockEntry.Explicit.triangleStockOrder C α κ η τ Λ h qMon


/-- On an already prescribed window, the basal split and monitored nibble
produce one packing, and the existing selector acts on *that same* physical
remainder. The exact seed of the deleted complement is explicit. -/
theorem positive_packing_on_fixed_prepared_window_with_triangle_monitors_explicit {I : Type}
    (F : Set (Multiset I)) (C α κ ηPack τ Λ τSel : ℝ) (h t qMon : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hκ : 0 < κ)
    (hη : 0 < ηPack) (hτ : 0 < τ) (hΛ : 0 < Λ)
    (ht : Odd t) (ht3 : 3 ≤ t) :
    ∀ {V : Type} [Fintype V]
      (H : Host V I) (ψ : Finset V → ℝ)
      (W : Finset V) (D DT : Finset (Finset V))
      (R T Bank E : Finset (Sym2 V)),
      triangleFixedPackingOrder C α κ ηPack τ Λ h qMon ≤ Fintype.card V →
      let B := (((cover D ∪ R) ∪ T) ∪ Bank) ∪ E
      let Jhost := subHost H (edges H \ B)
      S07V45.CorePathContract H.G H.lab F W t →
      IsDiffuseSeed Jhost F C ψ → IsPhysical Jhost F (edges Jhost) →
      CommonNbrCond Jhost F α → HingeCond Jhost F α h →
      IsPhysical H F (edges H) →
      IsDecomposition H F (cover D) D →
      Basal H F R → IsDecomposition H F T DT →
      Basal H F Bank → Basal H F E →
      Disjoint (cover D) T →
      Disjoint R (cover D ∪ T) →
      Disjoint Bank ((cover D ∪ R) ∪ T) →
      Disjoint E (((cover D ∪ R) ∪ T) ∪ Bank) →
      (∀ u v, H.G.Adj u v →
        κ * Fintype.card V ≤ (good H F D u v).card) →
      (∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
        ∃ Ps Y : Finset (Sym2 V), R ∪ L = Ps ∪ Y ∧
          Disjoint Ps Y ∧ Basal H F Ps ∧
          (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
          (∀ v, (SelSimul.edeg Y v : ℝ) ≤ τSel * Fintype.card V) ∧
          IsPhysical H F Y) →
      ∀ (κi ι ν : Type) [Fintype κi] [Fintype ι] [Fintype ν]
        (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
        (full : ι → Sym2 V → ℝ) (w : ν → Finset V → ℝ),
        ((Fintype.card κi + Fintype.card ι + Fintype.card ν : ℕ) : ℝ) ≤
          (Fintype.card V:ℝ)^qMon →
        (∀ k A, IsAllowed H F A →
          |triSum (loc k) A| ≤ 3 * Λ * (A ∩ bad k).card) →
        (∀ j A, IsAllowed H F A →
          |triSum (full j) A| ≤ 3 * Λ * A.card) →
        (∀ k A, IsAllowed H F A → |w k A| ≤ 1) →
        ∃ (P₀ DR Q : Finset (Finset V))
          (Rtail Ps Y : Finset (Sym2 V))
          (x : MCore H.G H.lab F W) (d q : ℕ),
          P₀ ⊆ Q ∧ IsPacking H F P₀ ∧
          (∀ A ∈ P₀, IsAllowed Jhost F A) ∧
          (∀ v, (((edges Jhost\P₀.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ ηPack*Fintype.card V) ∧
          (∀ k, |(∑ A ∈ P₀, w k A)-(∑ A ∈ allowed Jhost F, ψ A*w k A)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
          IsDecomposition H F Rtail DR ∧
          Disjoint (cover D) Rtail ∧ cover D ∪ Rtail = B ∧
          IsPacking H F Q ∧ Disjoint (Q.biUnion triEdges) Rtail ∧
          (edges H \ (Rtail ∪ Q.biUnion triEdges)) ⊆ cover D ∧
          IsPhysical H F (edges H \ (Rtail ∪ Q.biUnion triEdges)) ∧
          R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) = Ps ∪ Y ∧
          Disjoint Ps Y ∧ Basal H F Ps ∧ IsPhysical H F Y ∧
          (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
          (∀ v, (SelSimul.edeg Y v : ℝ) ≤ τSel * Fintype.card V) ∧
          (x : Sym2 V → ℤ) = SparseEdge.ind Y ∧
          clsQ H.G H.lab F W (x : Sym2 V → ℤ) ∈
            KZ H.G H.lab F W ∅ ∧
          ((2*d+2*q : ℕ) : ℝ) ≤ ηPack * Fintype.card V ∧
          (∀ k, |edgeSum (loc k)
              (edges H \ (Rtail ∪ Q.biUnion triEdges)) -
              edgeSum (loc k) (cover D)| ≤
            τ * Fintype.card V * (bad k).card +
              (3 * Λ * (bad k).card) * (2*d+2*q : ℕ) / 2) ∧
          ∀ j, |edgeSum (full j)
              (edges H \ (Rtail ∪ Q.biUnion triEdges)) -
              edgeSum (full j) (cover D)| ≤
            τ * (Fintype.card V : ℝ)^2 +
              (3 * Λ * Fintype.card V) * (2*d+2*q : ℕ) / 2 := by
  intro V _ H ψ W D DT R T Bank E hn
  dsimp only
  intro hPath hSeed hPhysJ h3 h4 hPhys hD hR hT hBank hE
    hDT hRDT hBankDis hEDis hSupply hMode
    κi ι ν _ _ _ bad loc full w hCount hLoc hFull hw
  obtain ⟨P₀,DR,Q,Rtail,hPQ,hP₀,hAllow,hSparse,hQuota,hDR,hDtail,hEq,hQ,hQR,hRes,hPhysRes,
    d,q,hLoad,hLocOut,hFullOut⟩ :=
    CatalogNative.Explicit.nibble_after_basal_remainder_split_with_triangle_monitors_explicit F C α κ ηPack τ Λ h qMon
      hC hα hκ hη hτ hΛ H ψ D DT R T Bank E hn hSeed hPhysJ h3 h4 hPhys
      hD hR hT hBank hE hDT hRDT hBankDis hEDis hSupply
      κi ι ν bad loc full w hCount hLoc hFull hw
  obtain ⟨Ps,Y,hMove,hPY,hPs,hYin,hYdeg,hYphys⟩ :=
    hMode (edges H \ (Rtail ∪ Q.biUnion triEdges)) hRes hPhysRes
  have hRE : R ⊆ edges H := CorePaid.basal_subset_edges hR
  have hYE : Y ⊆ edges H := by
    intro e heY
    have heRL : e ∈ R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) := by
      rw [hMove]
      exact mem_union_right _ heY
    rcases mem_union.mp heRL with heR | heL
    · exact hRE heR
    · exact (mem_sdiff.mp heL).1
  have hYsub : Y ⊆ SparseEdge.edges (indG H.G W) :=
    g4_positive_payload_in_child H W Y hYE hYin
  obtain ⟨x,hx,hCharge⟩ :=
    actual_physical_residue_charge H F hPath ht ht3 Y hYphys hYsub
  exact ⟨P₀,DR,Q,Rtail,Ps,Y,x,d,q,hPQ,hP₀,hAllow,hSparse,hQuota,hDR,hDtail,hEq,hQ,hQR,hRes,
    hPhysRes,hMove,hPY,hPs,hYphys,hYin,hYdeg,hx,hCharge,hLoad,
    hLocOut,hFullOut⟩

#print axioms positive_packing_on_fixed_prepared_window_with_triangle_monitors_explicit

end TypedTriangle.Vortex.Explicit
