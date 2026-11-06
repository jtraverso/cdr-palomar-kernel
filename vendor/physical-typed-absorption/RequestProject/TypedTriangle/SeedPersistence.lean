/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.CertProvider
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# P06 de extremo a extremo — persistencia de la semilla tras borrar un packing disperso

Se empalman explícitamente el proveedor concreto (`provK_hyp_disp`), el borde
(`bdry_kcert`), el soporte (`kcert_support`), la dispersión (`kcert_hL`), el transporte
(`transport_identity_residual`, `transport_error_avg_local`) y la positividad
(`seed_positivity`, constante `16b + 4`).

* `seed_persistence_approx`: entrada `μ` con `a/n ≤ μ_T ≤ b/n` en los triángulos
  permitidos y cargas `1 ± e` (`e ≤ 1/2`); `B` es un packing (con descomposición `Q`) de
  grado `≤ d ≤ ε₀ n`. Salida `ψ` soportada en los triángulos permitidos de `J = E ∖ B` con
  `a/(2n) ≤ ψ ≤ (b + a/2)/n` en ellos y `|A_J ψ − 1| ≤ (1 + 2·(4b)·d/n) e` en cada arista
  de `J`.
* `seed_persistence_exact`: con (H1) de constante `C`, la salida es una semilla exacta difusa
  del residual de constante `2C`.

`ε₀` y `n₀` dependen sólo de `(a, b, α, h)` (resp. `(C, α, h)`): se fijan antes del host,
de `B`, de `Q` y de la demanda. No se usa (H2), (H3) ni la física del host.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-- Pivote restringido a las aristas borradas. -/
def pivB (K : KData V) (B : Finset (Sym2 V)) (f : Sym2 V) (S : Finset V) : ℝ :=
  if f ∈ B then pivK K f S else 0

omit [Fintype V] in
lemma pivotTermW_pivB {H : Host V I} {F : Set (Multiset I)} [Fintype V] (K : KData V)
    (B : Finset (Sym2 V)) (T : Finset V) (e : Sym2 V) :
    pivotTermW H F B (pivB K B) T e = pivotTermW H F B (pivK K) T e := by
  unfold pivotTermW
  refine sum_congr rfl fun f hf => ?_
  congr 2; funext S; simp [pivB, hf]

omit [Fintype V] in
lemma pivK_le {K : KData V} {f : Sym2 V} (hne : (K.Piv f).Nonempty)
    (hnot : ∀ b ∈ K.Piv f, b ∉ f) (S : Finset V) :
    pivK K f S ≤ 1 / (K.Piv f).card := by
  unfold pivK
  rw [avgOver_ite]
  have hP0 : (0 : ℝ) < (K.Piv f).card := by exact_mod_cast card_pos.2 hne
  have h1 : ((K.Piv f).filter (fun b => S = insert b f.toFinset)).card ≤ 1 := by
    rw [card_le_one]
    intro b hb b' hb'
    rw [mem_filter] at hb hb'
    have h := hb.2.symm.trans hb'.2
    have : b ∈ insert b' f.toFinset := h ▸ mem_insert_self b _
    rcases mem_insert.1 this with h' | h'
    · exact h'
    · exact absurd (Sym2.mem_toFinset.1 h') (hnot b hb.1)
  rw [div_le_div_iff_of_pos_right hP0]
  exact_mod_cast h1

omit [Fintype V] in
lemma pivK_nonneg (K : KData V) (f : Sym2 V) (S : Finset V) : 0 ≤ pivK K f S := by
  unfold pivK; exact avgOver_nonneg fun b _ => by split_ifs <;> norm_num

omit [Fintype V] in
lemma residual_allowed {H : Host V I} {F : Set (Multiset I)} [Fintype V] {B : Finset (Sym2 V)}
    {T : Finset V} (hT : IsAllowed (residual H B) F T) :
    IsAllowed H F T ∧ Disjoint (triEdges T) B := by
  refine ⟨isAllowed_mono (subHost_le H _) rfl hT, ?_⟩
  rw [disjoint_left]
  intro e he heB
  have h1 := triEdges_subset_edges hT he
  induction e using Sym2.ind with
  | _ x y =>
    simp only [edges, residual, subHost, mem_filter, mem_univ, true_and,
      SimpleGraph.mem_edgeSet, SimpleGraph.inf_adj, SimpleGraph.fromEdgeSet_adj, coe_sdiff,
      Set.mem_diff, mem_coe] at h1
    exact h1.1.1.2 heB

/-- Constante de dispersión del proveedor. -/
def provL (α κ₀ : ℝ) (hh : ℕ) : ℝ :=
  2 ^ Nat.choose hh 2 / (α / 2) * ((1 + 3 * (2 * κ₀)) + (1 + 3 * (2 * κ₀)) ^ 2) *
    (1 + 2 * (1 + 3 * (2 * κ₀) + 3 * (2 ^ Nat.choose hh 2 / (α / 2))))

lemma provL_nonneg {α κ₀ : ℝ} (hα : 0 < α) (hκ : 0 ≤ κ₀) (hh : ℕ) : 0 ≤ provL α κ₀ hh := by
  unfold provL; positivity

/-- **Persistencia aproximada de la semilla (P06, versión cuantitativa).** -/
theorem seed_persistence_approx {F : Set (Multiset I)} {a b α : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hα : 0 < α) (hh : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, ∀ {W : Type*} [Fintype W] (H : Host W I) (μ : Finset W → ℝ)
      (B : Finset (Sym2 W)) (Q : Finset (Finset W)) (d : ℕ) (e : ℝ),
      n₀ ≤ Fintype.card W → HingeCond H F α hh →
      (∀ T, IsAllowed H F T → a / Fintype.card W ≤ μ T ∧ μ T ≤ b / Fintype.card W) →
      0 ≤ e → e ≤ 1 / 2 → (∀ f ∈ edges H, |bdry H F μ f - 1| ≤ e) →
      B ⊆ edges H → IsDecomposition H F B Q → (∀ x, degIn B x ≤ d) →
      (d : ℝ) ≤ ε₀ * Fintype.card W →
      ∃ ψ : Finset W → ℝ, (∀ S, ψ S ≠ 0 → IsAllowed (residual H B) F S) ∧
        (∀ S, IsAllowed (residual H B) F S →
          a / (2 * Fintype.card W) ≤ ψ S ∧ ψ S ≤ (b + a / 2) / Fintype.card W) ∧
        (∀ f ∈ edges H, f ∉ B →
          |bdry (residual H B) F ψ f - 1| ≤ (1 + 2 * d * (4 * b / Fintype.card W)) * e) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set κ₀ := 2 * b
  set L := provL α κ₀ hh
  have hL0 : 0 ≤ L := provL_nonneg hα (by positivity) hh
  set ε₀ := min (α / (10 * 2 ^ Nat.choose hh 2)) (min (1 / (32 * b))
    (a / (2 * (16 * b + 4) * (L + 1))))
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨ε₀, hε₀, ⌈16 * b⌉₊ + 1, ?_⟩
  intro W _ H μ B Q d e hn0 hcond hμ he0 he1 hload hB hQ hdeg hd
  have hn0' : ((⌈16 * b⌉₊ : ℕ) : ℝ) + 1 ≤ (Fintype.card W : ℝ) := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ Fintype.card W := by
    have : (1 : ℕ) ≤ Fintype.card W := by omega
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

/-- **Persistencia exacta de la semilla (P06).** Con (H1) de constante `C ≥ 1` y (H4), tras
borrar un packing `B` (descomposición `Q`) de grado `≤ d ≤ ε₀ n`, el residual `J = E ∖ B`
admite una semilla exacta difusa de constante `2C`, soportada en sus triángulos. -/
theorem seed_persistence_exact {F : Set (Multiset I)} {C α : ℝ} (hC : 1 ≤ C) (hα : 0 < α)
    (hh : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, ∀ {W : Type*} [Fintype W] (H : Host W I) (φ : Finset W → ℝ)
      (B : Finset (Sym2 W)) (Q : Finset (Finset W)) (d : ℕ),
      n₀ ≤ Fintype.card W → IsDiffuseSeed H F C φ → HingeCond H F α hh →
      B ⊆ edges H → IsDecomposition H F B Q → (∀ x, degIn B x ≤ d) →
      (d : ℝ) ≤ ε₀ * Fintype.card W →
      ∃ ψ : Finset W → ℝ, IsDiffuseSeed (residual H B) F (2 * C) ψ ∧
        (∀ S, ψ S ≠ 0 → IsAllowed (residual H B) F S) := by
  have hC0 : 0 < C := by linarith
  obtain ⟨ε₀, hε₀, n₀, h⟩ := seed_persistence_approx (F := F) (a := 1 / C) (b := C)
    (by positivity) (by rw [div_le_iff₀ hC0]; nlinarith) hα hh
  refine ⟨ε₀, hε₀, n₀, ?_⟩
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
  obtain ⟨ψ, hsupp, hpos, hld⟩ :=
    h H φ B Q d 0 hn0 hcond hμ le_rfl (by norm_num) hload hB hQ hdeg hd
  refine ⟨ψ, ⟨fun T hT => ?_, fun f hf => ?_⟩, hsupp⟩
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

end TypedTriangle
