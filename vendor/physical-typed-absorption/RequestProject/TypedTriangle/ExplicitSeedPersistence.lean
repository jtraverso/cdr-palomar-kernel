module
public import RequestProject.TypedTriangle.SeedPersistence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.RawReference.Explicit
variable {I : Type*}
def seedBudget (a b α : ℝ) (h : ℕ) : ℝ :=
  min (α / (10 * 2 ^ Nat.choose h 2)) (min (1 / (32 * b))
    (a / (2 * (16 * b + 4) * (provL α (2 * b) h + 1))))
def seedOrder (b : ℝ) : ℕ := ⌈16 * b⌉₊ + 1

theorem seedBudget_pos {a b α : ℝ} (h : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) : 0 < seedBudget a b α h := by
  have hb : 0 < b := ha.trans_le hab
  have hL := provL_nonneg hα (by positivity : 0 ≤ 2 * b) h
  unfold seedBudget
  positivity

/-- Original seed transport with its numerical budget and order exposed. -/
theorem seed_persistence_approx_explicit {F : Set (Multiset I)} {a b α : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hα : 0 < α) (hh : ℕ) :
    ∀ {W : Type*} [Fintype W] (H : Host W I) (μ : Finset W → ℝ)
      (B : Finset (Sym2 W)) (Q : Finset (Finset W)) (d : ℕ) (e : ℝ),
      seedOrder b ≤ Fintype.card W → HingeCond H F α hh →
      (∀ T, IsAllowed H F T → a / Fintype.card W ≤ μ T ∧ μ T ≤ b / Fintype.card W) →
      0 ≤ e → e ≤ 1 / 2 → (∀ f ∈ edges H, |bdry H F μ f - 1| ≤ e) →
      B ⊆ edges H → IsDecomposition H F B Q → (∀ x, degIn B x ≤ d) →
      (d : ℝ) ≤ seedBudget a b α hh * Fintype.card W →
      ∃ ψ : Finset W → ℝ, (∀ S, ψ S ≠ 0 → IsAllowed (residual H B) F S) ∧
        (∀ S, IsAllowed (residual H B) F S →
          a / (2 * Fintype.card W) ≤ ψ S ∧ ψ S ≤ (b + a / 2) / Fintype.card W) ∧
        (∀ f ∈ edges H, f ∉ B →
          |bdry (residual H B) F ψ f - 1| ≤ (1 + 2 * d * (4 * b / Fintype.card W)) * e) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set κ₀ := 2 * b
  set L := provL α κ₀ hh
  have hL0 : 0 ≤ L := provL_nonneg hα (by positivity) hh
  intro W _ H μ B Q d e hn0 hcond hμ he0 he1 hload hB hQ hdeg hd
  have hn0' : ((⌈16 * b⌉₊ : ℕ) : ℝ) + 1 ≤ (Fintype.card W : ℝ) := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ Fintype.card W := by
    have hc : (0 : ℝ) ≤ (⌈16 * b⌉₊ : ℕ) := by positivity
    linarith
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
  refine ⟨transported H F μ Q cert, hψsupp, ?_, ?_⟩
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


#print axioms seed_persistence_approx_explicit
end TypedTriangle.RawReference.Explicit
