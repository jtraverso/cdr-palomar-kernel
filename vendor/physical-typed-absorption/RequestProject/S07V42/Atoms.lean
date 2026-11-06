/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.Setting
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V42 §3 — bounded atoms of `M(H[W \ Z])` from the H3/H4 of the TRUE core subtype

Hypotheses: the ACTUAL induced core host `H[W] = H.comap (Subtype.val : {x // x ∈ W} → V)`
satisfies H3 with `β` and H4 with `(β, h)`. Nothing is assumed about `H` on `V \ W`, and no H3 is
claimed for the ambient zero extension `indG H W`.

* `coreDelta β h`, `coreN0 β h`, `atomR β` — constants fixed from `(β, h)` before the host.
* `subtype_H3H4_deleted`: for `|Z| ≤ coreDelta β h · |W|` the TRUE induced host
  `H[W \ Z] = H.comap (Subtype.val : {x // x ∈ W \ Z} → V)` satisfies H3 with `β/2` and H4 with
  `(β/2, h)` (from `commonNbr_deletion`, `hinge_deletion` applied to `{x // x ∈ W \ Z} → {x // x ∈ W}`).
* `bounded_atoms`: for such `Z` and `|W| ≥ coreN0 β h`, the ambient module
  `MZ = M(H[W \ Z])` (zero-extended) is spanned by its elements of `l1E ≤ atomR β`. Proof:
  V37 `routing_atoms_H3H4` on the true subtype host, transported by `isLocalProfile_pull` /
  `isLocalProfile_liftE`.
-/

open Finset Classical Submodule

noncomputable section

namespace S07V42

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal TypedTriangle.RoutingConstants
open S07V25 (n1Of)

/-- the admissible deletion rate, fixed from `(β, h)` -/
def coreDelta (β : ℝ) (h : ℕ) : ℝ := min (1 / 2) (β / (2 * 2 ^ (h.choose 2)))

/-- the core size threshold, fixed from `(β, h)` -/
def coreN0 (β : ℝ) (h : ℕ) : ℕ := 2 * (routeN0 (β / 2) h + n1Of (β / 2))

/-- the atom size, fixed from `β` -/
def atomR (β : ℝ) : ℕ := 3 * routeD (β / 2)

lemma coreDelta_nonneg {β : ℝ} (hβ : 0 < β) (h : ℕ) : 0 ≤ coreDelta β h :=
  le_min (by norm_num) (by positivity)

lemma coreDelta_le_half (β : ℝ) (h : ℕ) : coreDelta β h ≤ 1 / 2 := min_le_left _ _

lemma coreDelta_mul_le {β : ℝ} (hβ : 0 < β) (h : ℕ) :
    coreDelta β h * 2 ^ (h.choose 2) ≤ β / 2 := by
  have hp : (0 : ℝ) < 2 ^ (h.choose 2) := by positivity
  calc coreDelta β h * 2 ^ (h.choose 2) ≤ β / (2 * 2 ^ (h.choose 2)) * 2 ^ (h.choose 2) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hp.le
    _ = β / 2 := by field_simp

lemma coreDelta_le {β : ℝ} (hβ : 0 < β) (h : ℕ) : coreDelta β h ≤ β / 2 := by
  have h1 : (1 : ℝ) ≤ 2 ^ (h.choose 2) := one_le_pow₀ (by norm_num)
  have := coreDelta_mul_le hβ h
  have h0 := coreDelta_nonneg hβ h
  nlinarith

variable {V I : Type*} [Fintype V] (H : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
  (W : Finset V)

/-- the inclusion of the deleted core into the core -/
def delIncl (Z : Finset V) : {x // x ∈ W \ Z} → {x // x ∈ W} :=
  fun y => ⟨y.1, (Finset.mem_sdiff.1 y.2).1⟩

omit [Fintype V] in
lemma delIncl_injective (Z : Finset V) : Function.Injective (delIncl W Z) :=
  fun _ _ h => Subtype.ext (congrArg Subtype.val h :)

omit [Fintype V] in
lemma delIncl_range (Z : Finset V) (x : {x // x ∈ W}) :
    (∃ y, delIncl W Z y = x) ↔ x ∉ univ.filter (fun x : {x // x ∈ W} => x.1 ∈ Z) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, rfl⟩; exact (Finset.mem_sdiff.1 y.2).2
  · intro hx; exact ⟨⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hx⟩⟩, rfl⟩

omit [Fintype V] in
lemma card_Zx_le (Z : Finset V) :
    (univ.filter (fun x : {x // x ∈ W} => x.1 ∈ Z)).card ≤ Z.card := by
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  exact hx

omit [Fintype V] in
/-- **H3/H4 on the TRUE deleted core subtype.** -/
theorem subtype_H3H4_deleted {β : ℝ} {h : ℕ} (hβ : 0 < β)
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    {Z : Finset V} (hZ : (Z.card : ℝ) ≤ coreDelta β h * W.card) :
    CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W \ Z} → V)) (lab ∘ Subtype.val) F
        (β / 2) ∧
      HingeCond (H.comap (Subtype.val : {x // x ∈ W \ Z} → V)) (lab ∘ Subtype.val) F
        (β / 2) h := by
  have hZx : ((univ.filter (fun x : {x // x ∈ W} => x.1 ∈ Z)).card : ℝ) ≤
      coreDelta β h * Fintype.card {x // x ∈ W} := by
    rw [Fintype.card_coe]
    exact (Nat.cast_le.2 (card_Zx_le W Z)).trans hZ
  exact ⟨commonNbr_deletion (delIncl_injective W Z) (delIncl_range W Z) hβ hH3 hZx
      (coreDelta_le hβ h),
    hinge_deletion (delIncl_injective W Z) (delIncl_range W Z) hβ hH4 hZx
      (coreDelta_nonneg hβ h) (coreDelta_mul_le hβ h)⟩

omit [Fintype V] in
lemma card_sdiff_ge {β : ℝ} {h : ℕ} {Z : Finset V}
    (hZ : (Z.card : ℝ) ≤ coreDelta β h * W.card) : W.card ≤ 2 * (W \ Z).card := by
  have h1 : (Z.card : ℝ) ≤ W.card / 2 := by
    have := coreDelta_le_half β h
    have h0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
    nlinarith
  have h2 : W.card ≤ (W \ Z).card + Z.card := by
    have := Finset.card_sdiff_add_card_inter W Z
    have h3 := Finset.card_le_card (Finset.inter_subset_right (s₁ := W) (s₂ := Z))
    omega
  have h4 : (W.card : ℝ) ≤ (W \ Z).card + Z.card := by exact_mod_cast h2
  have : (W.card : ℝ) ≤ 2 * (W \ Z).card := by linarith
  exact_mod_cast this

/-- the bounded atoms of `M(H[W \ Z])` -/
def atomsZ (β : ℝ) (Z : Finset V) : Set (Sym2 V → ℤ) :=
  {b | b ∈ MZ H lab F W Z ∧ l1E b ≤ atomR β}

/-- **Bounded atoms span `M(H[W \ Z])`** (subtype adapter around V37 routing). -/
theorem bounded_atoms {β : ℝ} {h : ℕ} (hβ : 0 < β)
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card)
    {Z : Finset V} (hZ : (Z.card : ℝ) ≤ coreDelta β h * W.card) :
    atomsZ H lab F W β Z ⊆ MZ H lab F W Z ∧ MZ H lab F W Z ≤ span ℤ (atomsZ H lab F W β Z) := by
  refine ⟨fun b hb => hb.1, ?_⟩
  obtain ⟨hY3, hY4⟩ := subtype_H3H4_deleted H lab F W hβ hH3 hH4 hZ
  have hcard := card_sdiff_ge W hZ
  have hYc : Fintype.card {x // x ∈ W \ Z} = (W \ Z).card := Fintype.card_coe _
  have hn0 : routeN0 (β / 2) h ≤ Fintype.card {x // x ∈ W \ Z} := by
    rw [hYc]; unfold coreN0 at hW; omega
  have hn1 : n1Of (β / 2) ≤ Fintype.card {x // x ∈ W \ Z} := by
    rw [hYc]; unfold coreN0 at hW; omega
  obtain ⟨-, hspan⟩ := S07V37.routing_atoms_H3H4 (by positivity) hY3 hY4 hn0 hn1
  have hι : Function.Injective (Subtype.val : {x // x ∈ W \ Z} → V) := Subtype.val_injective
  have hG := edgesIn_indG H (W \ Z)
  have hcomap := indG_comap H (W \ Z)
  intro x hx
  have hx' : IsLocalProfile (indG H (W \ Z)) lab F x := hx
  obtain ⟨hpull, hlift⟩ := isLocalProfile_pull hι hG hx'
  rw [hcomap] at hpull
  have hmem := hspan (show (x ∘ Sym2.map Subtype.val) ∈ localProfile _ _ F from hpull)
  rw [← hlift]
  have hmap : liftL Subtype.val hι '' S07V37.atoms (H.comap Subtype.val)
      (lab ∘ Subtype.val) F (β / 2) ⊆ atomsZ H lab F W β Z := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨?_, ?_⟩
    · show IsLocalProfile (indG H (W \ Z)) lab F (liftE (ι := Subtype.val) b)
      apply isLocalProfile_liftE hι hG
      rw [hcomap]; exact hb.1
    · rw [liftL_apply, l1E_liftE hι]
      exact_mod_cast hb.2
  have := Submodule.mem_map_of_mem (f := liftL Subtype.val hι) hmem
  rw [Submodule.map_span] at this
  exact span_mono hmap this

end S07V42
