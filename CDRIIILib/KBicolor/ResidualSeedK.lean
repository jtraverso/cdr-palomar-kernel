/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.BRIkGlue
public import CDRIIILib.KBicolor.ResidualHinge
public import CDRIIILib.KBicolor.ExactMass

/-!
# Residual seeds with controlled type masses (`k` classes)

* `wlk_tri`, `MincG_seed_one_k`, `hell1_k`: the functional `ℓ` vanishes on bicoloured
  triangles and on the all-ones vector;
* `mass_residual_k`: passing from a complete seed `μ₀` to `gm L (μ₀ + ψ)` changes the mass of any
  weight `0 ≤ w ≤ 1` by at most `n³ r + n² Δ C₀ / n`;
* `residual_seed_k`: from seed data `a`, the `k`-class bounded right inverse (`briK`) and a
  packing with leave degree `≤ Δ`, a diffuse seed of `K_n − L` whose mass of every type `XXY`
  is `c_X c_Y a_XY / 2` up to `(4K + 1) C₀ Δ n`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

theorem wlk_tri (lab : V → Fin k) {T : Finset V} (hT : T ∈ triG lab (bicF k)) :
    ∑ f ∈ triEdges T, wlk lab f = 0 := by
  have hA : IsAllowed (cHostG lab) (bicF k) T := gmem_tri.mp hT
  obtain ⟨h3, -, hF⟩ := hA
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp h3
  have hlab : ({lab x, lab y, lab z} : Multiset (Fin k)) ∈ bicF k := by
    have : ({x, y, z} : Finset V).val.map lab ∈ bicF k := hF
    rwa [val_map_triple lab hxy hxz.symm hyz.symm] at this
  rw [triEdges_triple hxy hxz hyz, sum_insert (by simp [hyz, hxz]),
    sum_insert (by simp [hxy, hxz]), sum_singleton]
  simp only [wlk, Sym2.lift_mk]
  rcases mem_bicF.1 hlab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg (by rw [h1]; exact h2), if_neg h2]; norm_num
  · rw [if_neg h2, if_pos h1, if_neg (by rw [← h1]; exact fun h => h2 h.symm)]; norm_num
  · rw [if_neg h2, if_neg (by rw [← h1]; exact h2), if_pos h1]; norm_num

theorem MincG_seed_one_k (lab : V → Fin k) {μ : Finset V → ℝ} {C : ℝ}
    (hμ : IsDiffuseSeed (kHost lab) (bicF k) C μ) (e : E0 V) :
    MincG lab (bicF k) μ e = 1 := by
  have he : e.1 ∈ (kHost lab).G.edgeSet := by
    show e.1 ∈ (⊤ : SimpleGraph V).edgeSet
    rw [SimpleGraph.edgeSet_top]; exact e.2
  have := hμ.2 e.1 he
  simp only [MincG, LinearMap.coe_mk, AddHom.coe_mk]
  convert this using 2
  ext T
  simp only [mem_filter]

theorem hell1_k (lab : V → Fin k) {μ : Finset V → ℝ} {C : ℝ}
    (hμ : IsDiffuseSeed (kHost lab) (bicF k) C μ) :
    ellG' (wlk lab) (fun _ => 1) = 0 := by
  have : (fun _ : E0 V => (1 : ℝ)) = MincG lab (bicF k) μ :=
    funext fun e => (MincG_seed_one_k lab hμ e).symm
  rw [this, gell_M (fun T hT => wlk_tri lab hT)]

theorem allowed_rHostK_eq (lab : V → Fin k) (L : Finset (Sym2 V)) :
    allowed (rHostK lab L) (bicF k) = (triG lab (bicF k)).filter fun T => Disjoint (triEdges T) L := by
  ext T
  have h := gallowed_iff (lab := lab) (F := bicF k) (L := L) (T := T)
  classical
  unfold allowed
  simp only [mem_filter, mem_univ, true_and]
  exact h

theorem card_triG_le (lab : V → Fin k) :
    (#(triG lab (bicF k)) : ℝ) ≤ (Fintype.card V : ℝ) ^ 3 := by
  have hsub : triG lab (bicF k) ⊆ (univ : Finset V).powersetCard 3 := by
    intro T hT
    rw [mem_powersetCard]
    exact ⟨subset_univ _, (gmem_tri.mp hT).1⟩
  have h1 := card_le_card hsub
  rw [card_powersetCard, card_univ] at h1
  have h2 := h1.trans (Nat.choose_le_pow _ _)
  exact_mod_cast h2

theorem card_bad_le_k (lab : V → Fin k) (L : Finset (Sym2 V)) {Δ : ℕ}
    (hdeg : ∀ p, degL L p ≤ Δ) :
    (#((triG lab (bicF k)).filter fun T => ¬ Disjoint (triEdges T) L) : ℝ) ≤
      (Fintype.card V : ℝ) ^ 2 * Δ := by
  have hsub : ((triG lab (bicF k)).filter fun T => ¬ Disjoint (triEdges T) L) ⊆
      (univ : Finset V).biUnion fun v => (nbL L v).biUnion fun w =>
        (univ : Finset V).image fun x => ({v, w, x} : Finset V) := by
    intro T hT
    obtain ⟨hTt, hbad⟩ := mem_filter.mp hT
    obtain ⟨e, he, heL⟩ := not_disjoint_iff.mp hbad
    induction e using Sym2.ind with
    | _ v w =>
    simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he
    obtain ⟨⟨hv, hw⟩, hvw⟩ := he
    obtain ⟨x, -, -, hTx⟩ := third_vertex (gmem_tri.mp hTt).1 hvw hv hw
    simp only [mem_biUnion, mem_univ, true_and, mem_image]
    refine ⟨v, w, ?_, x, hTx.symm⟩
    simp only [nbL, mem_filter, mem_univ, true_and]
    rwa [Sym2.eq_swap]
  have hc := card_le_card hsub
  set n := Fintype.card V
  have h2 : #((univ : Finset V).biUnion fun v => (nbL L v).biUnion fun w =>
      (univ : Finset V).image fun x => ({v, w, x} : Finset V)) ≤ n * (Δ * n) := by
    calc _ ≤ ∑ v : V, #((nbL L v).biUnion fun w =>
          (univ : Finset V).image fun x => ({v, w, x} : Finset V)) := card_biUnion_le
      _ ≤ ∑ _v : V, Δ * n := by
          gcongr with v
          calc _ ≤ ∑ w ∈ nbL L v, #((univ : Finset V).image
                fun x => ({v, w, x} : Finset V)) := card_biUnion_le
            _ ≤ ∑ _w ∈ nbL L v, n := by
                gcongr with w; exact card_image_le.trans (by simp [n])
            _ = #(nbL L v) * n := by rw [sum_const, smul_eq_mul]
            _ ≤ Δ * n := Nat.mul_le_mul_right _ (by have := hdeg v; unfold degL at this; exact this)
      _ = n * (Δ * n) := by simp [sum_const, card_univ, n]
  have : (#((triG lab (bicF k)).filter fun T => ¬ Disjoint (triEdges T) L) : ℝ) ≤
      (((n * (Δ * n)) : ℕ) : ℝ) := by exact_mod_cast hc.trans h2
  have e : (((n * (Δ * n)) : ℕ) : ℝ) = (n : ℝ) ^ 2 * Δ := by push_cast; ring
  linarith

/-- **Mass of a residual seed** (any weight `0 ≤ w ≤ 1`). -/
theorem mass_residual_k (lab : V → Fin k) (L : Finset (Sym2 V)) {Δ : ℕ}
    (hdeg : ∀ p, degL L p ≤ Δ) {μ₀ ψ : Finset V → ℝ} {r C₀ : ℝ} (hψ : ∀ T, |ψ T| ≤ r)
    (hμ₀ : ∀ T ∈ triG lab (bicF k), |μ₀ T| ≤ C₀ / (Fintype.card V : ℝ)) (hC₀ : 0 ≤ C₀)
    (w : Finset V → ℝ) (hw : ∀ Q, 0 ≤ w Q ∧ w Q ≤ 1) :
    |∑ Q ∈ allowed (rHostK lab L) (bicF k), gm L (μ₀ + ψ) Q * w Q -
        ∑ Q ∈ allowed (kHost lab) (bicF k), μ₀ Q * w Q| ≤
      (Fintype.card V : ℝ) ^ 3 * r + (Fintype.card V : ℝ) ^ 2 * Δ * (C₀ / (Fintype.card V : ℝ)) := by
  have hr : 0 ≤ r := (abs_nonneg _).trans (hψ ∅)
  rw [allowed_rHostK_eq, show allowed (kHost lab) (bicF k) = triG lab (bicF k) from rfl]
  set S := triG lab (bicF k)
  set n : ℝ := (Fintype.card V : ℝ)
  have hsplit : ∑ Q ∈ S, μ₀ Q * w Q =
      ∑ Q ∈ S.filter (fun T => Disjoint (triEdges T) L), μ₀ Q * w Q +
        ∑ Q ∈ S.filter (fun T => ¬ Disjoint (triEdges T) L), μ₀ Q * w Q :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have hgood : ∀ Q ∈ S.filter (fun T => Disjoint (triEdges T) L),
      gm L (μ₀ + ψ) Q * w Q = μ₀ Q * w Q + ψ Q * w Q := by
    intro Q hQ
    simp only [gm, LinearMap.coe_mk, AddHom.coe_mk, if_pos (mem_filter.mp hQ).2, Pi.add_apply]
    ring
  rw [sum_congr rfl hgood, sum_add_distrib, hsplit]
  have e : ∀ x y z : ℝ, x + y - (x + z) = y - z := fun _ _ _ => by ring
  rw [e]
  have h1 : |∑ Q ∈ S.filter (fun T => Disjoint (triEdges T) L), ψ Q * w Q| ≤ n ^ 3 * r := by
    calc _ ≤ ∑ Q ∈ S.filter (fun T => Disjoint (triEdges T) L), |ψ Q * w Q| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _Q ∈ S.filter (fun T => Disjoint (triEdges T) L), r := by
          gcongr with Q
          rw [abs_mul, abs_of_nonneg (hw Q).1]
          nlinarith [hψ Q, (hw Q).2, abs_nonneg (ψ Q)]
      _ = #(S.filter fun T => Disjoint (triEdges T) L) * r := by rw [sum_const, nsmul_eq_mul]
      _ ≤ #S * r := by gcongr; exact filter_subset _ _
      _ ≤ _ := by gcongr; exact card_triG_le lab
  have h2 : |∑ Q ∈ S.filter (fun T => ¬ Disjoint (triEdges T) L), μ₀ Q * w Q| ≤
      n ^ 2 * Δ * (C₀ / n) := by
    calc _ ≤ ∑ Q ∈ S.filter (fun T => ¬ Disjoint (triEdges T) L), |μ₀ Q * w Q| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _Q ∈ S.filter (fun T => ¬ Disjoint (triEdges T) L), C₀ / n := by
          gcongr with Q hQ
          rw [abs_mul, abs_of_nonneg (hw Q).1]
          have := hμ₀ Q (mem_filter.mp hQ).1
          nlinarith [(hw Q).2, abs_nonneg (μ₀ Q)]
      _ = #(S.filter fun T => ¬ Disjoint (triEdges T) L) * (C₀ / n) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (card_bad_le_k lab L hdeg)
          (div_nonneg hC₀ (Nat.cast_nonneg _))
  calc _ ≤ |∑ Q ∈ S.filter (fun T => Disjoint (triEdges T) L), ψ Q * w Q| +
        |∑ Q ∈ S.filter (fun T => ¬ Disjoint (triEdges T) L), μ₀ Q * w Q| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

/-- The type weight `[Q has type XXY]`. -/
def wXY (lab : V → Fin k) (X Y : Fin k) (Q : Finset V) : ℝ :=
  if Q.val.map lab = {X, X, Y} then 1 else 0

theorem wXY_bounds (lab : V → Fin k) (X Y : Fin k) (Q : Finset V) :
    0 ≤ wXY lab X Y Q ∧ wXY lab X Y Q ≤ 1 := by
  unfold wXY; split_ifs <;> norm_num

/-- **Residual seed with controlled type masses.** -/
theorem residual_seed_k (lab : V → Fin k) (hk : 3 ≤ k) (o : Fin k) {m : ℕ} {R δ η : ℝ}
    (hR : 1 ≤ R) (hm : ∀ X, m ≤ ksz lab X) (h512 : 512 ≤ m) (hmR : 64 * R ^ 3 ≤ m)
    (hbal : (Fintype.card V : ℝ) ≤ R * m) (hδ : 0 < δ) (hη : 0 < η)
    (hcls : ∀ X, δ * Fintype.card V ≤ ksz lab X) (h2 : 2 ≤ δ * Fintype.card V)
    {a : Fin k → Fin k → ℝ} (ha : SeedData (ksz lab) η a)
    (P : Finset (Finset V)) (hP : ∀ T ∈ P, IsAllowed (kHost lab) (bicF k) T)
    (hPd : (P : Set (Finset V)).PairwiseDisjoint triEdges) {Δ : ℕ}
    (hdeg : ∀ p, degL (P.biUnion triEdges) p ≤ Δ)
    (hΔ : 8 * ((#(Trip o) : ℝ) * (400 * R ^ 5 * R * (1 + 4 * R ^ 2))) *
      (1 / η + 2 / δ) ^ 2 * Δ ≤ Fintype.card V) :
    ∃ μ, IsDiffuseSeed (rHostK lab (P.biUnion triEdges)) (bicF k) (2 * (1 / η + 2 / δ)) μ ∧
      ∀ X Y, X ≠ Y →
        |∑ Q ∈ allowed (rHostK lab (P.biUnion triEdges)) (bicF k), μ Q * wXY lab X Y Q -
          (ksz lab X : ℝ) * ksz lab Y * a X Y / 2| ≤
        (4 * ((#(Trip o) : ℝ) * (400 * R ^ 5 * R * (1 + 4 * R ^ 2))) + 1) *
          (1 / η + 2 / δ) * Δ * Fintype.card V := by
  set K : ℝ := (#(Trip o) : ℝ) * (400 * R ^ 5 * R * (1 + 4 * R ^ 2)) with hK
  set C₀ : ℝ := 1 / η + 2 / δ with hC₀
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hC1 : 1 ≤ C₀ := by
    have : 2 ≤ 2 / δ := by
      rw [le_div_iff₀ hδ]
      have : δ ≤ 1 := by
        have h1 := hcls ⟨0, by omega⟩
        have : (ksz lab ⟨0, by omega⟩ : ℝ) ≤ Fintype.card V := by
          have : ksz lab ⟨0, by omega⟩ ≤ Fintype.card V := by
            unfold ksz; exact (card_filter_le _ _).trans_eq card_univ
          exact_mod_cast this
        have hn : (0 : ℝ) < Fintype.card V := by
          have := h2; nlinarith
        nlinarith
      linarith
    have : 0 < 1 / η := by positivity
    rw [hC₀]; linarith
  obtain ⟨B⟩ := briK lab hk o hR hm h512 hmR hbal
  have hseed := kH1 lab hη hδ ha hcls h2
  set μ₀ : Finset V → ℝ := fun T => seedW (ksz lab) a (T.val.map lab)
  have hNpos : 0 < Fintype.card V := by
    have : (0 : ℝ) < Fintype.card V := by nlinarith
    exact_mod_cast this
  have hP' : ∀ T ∈ P, T ∈ triG lab (bicF k) := fun T hT => gmem_tri.mpr (hP T hT)
  have hρ := gMinc_indP P hP' hPd
  obtain ⟨μ, ψ, hμ, rfl, hψ⟩ := gen_residual_seed' (P.biUnion triEdges)
    (lab := lab) (F := bicF k) (w := wlk lab)
    (fun T hT => wlk_tri lab hT) (K := K) (C₀ := C₀) (η := 0) hK0 hC1 le_rfl
    B (hell1_k lab hseed) (μ₀ := μ₀) (fun T hT => hseed.1 T (gmem_tri.mp hT))
    (fun e => by rw [MincG_seed_one_k lab hseed e]; simp) _ hρ hdeg hNpos
    (by simpa using hΔ)
  refine ⟨_, hμ, fun X Y hXY => ?_⟩
  have hb0 : ∀ T ∈ triG lab (bicF k), |μ₀ T| ≤ C₀ / (Fintype.card V : ℝ) := by
    intro T hT
    obtain ⟨l, u⟩ := hseed.1 T (gmem_tri.mp hT)
    rw [abs_of_nonneg (le_trans (by positivity) l)]
    exact u
  have hm' := mass_residual_k lab (P.biUnion triEdges) hdeg hψ hb0 (by linarith)
    (wXY lab X Y) (wXY_bounds lab X Y)
  have hc2 : 2 ≤ ksz lab X := by
    have : (2 : ℝ) ≤ ksz lab X := le_trans h2 (hcls X)
    exact_mod_cast this
  have htot : ∑ Q ∈ allowed (kHost lab) (bicF k), μ₀ Q * wXY lab X Y Q =
      (ksz lab X : ℝ) * ksz lab Y * a X Y / 2 := seed_mass lab a hXY hc2
  rw [htot] at hm'
  refine hm'.trans (le_of_eq ?_)
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast hNpos
  field_simp
  ring

end CDRBicolour.KBicolor
