/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Broom

/-!
# Kites without `c`, part A: the second closing argument

Chen–Cao (arXiv:2512.07252), proof of Lemma 4.2, last paragraph. In the normal form of a kite
without `c` (`φ(bu) = α`, `φ(us₁) = β` missing at `b`, `φ(us₂) = δ ∈ φ̄(a)`,
`φ(s₁t₁) = φ(s₂t₂) = γ ∈ φ̄(a)`, `t₁, t₂` missing `β, δ`), suppose that after uncolouring `us₂` the
`(β, δ)`-chain of `u` ends at `b`. Uncolour `us₁` instead, swap the `(β, δ)`-chain of `s₁` (it ends
at `b`) and colour `ab` by `δ`: a colouring of `G − us₁` in which `(u; s₁, s₂)` is a multifan.
Since `u, t₁, t₂` miss `β`, one of `t₁, t₂` is not `(β, γ)`-linked with `u`:
* not `t₁`: swap its `(β, γ)`-chain, recolour `s₁t₁` by `δ`, colour `us₁` by `β`;
* not `t₂`: swap its `(β, γ)`-chain; then `u s₂ t₂` is a `(β, δ)`-chain from `u` to `t₂`, while
  `u` and `s₁` are `(β, δ)`-linked.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The multifan `(u; s₁, s₂)` of a colouring of `G − us₁` links `u` and `s₁`. -/
theorem fan2_link₀ (hG : IsClassTwo G) {d : PEC G (Fin G.maxDegree)} {u x y : V}
    (hcm : IsColMinus d u x) {δ : Fin G.maxDegree} (huy : d.col u y = some δ)
    (hxδ : d.IsFree x δ) (hxy : x ≠ y) {θ η : Fin G.maxDegree} (hu : d.IsFree u θ)
    (hx : d.IsFree x η) : (d.kempeGraph θ η).Reachable u x := by
  have hF : IsMultifan d u 2 (fun i => if i = 0 then x else y) := by
    refine ⟨by omega, by simp only [if_true]; exact hcm.uncol, fun i hi => ?_,
      fun i hi j hj hij => ?_, fun i hi0 hi => ?_⟩
    · split_ifs
      · exact hcm.adj
      · exact d.col_adj huy
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rfl
      · exact absurd hij (by simpa using hxy)
      · exact absurd hij (by simpa using hxy.symm)
      · rfl
    · refine ⟨0, hi0, δ, ?_, by simpa using hxδ⟩
      simp only [show i ≠ 0 by omega, if_false]
      exact huy
  obtain ⟨-, -, hB⟩ := multifan_elementary hG 2 d u _ hcm hF
  simpa using hB 0 (by omega) θ η hu (by simpa using hx)

set_option maxHeartbeats 4000000 in
/-- **The second closing argument.** -/
theorem z_close (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u s₁ s₂ t₁ t₂ : V}
    (hd : Distinct7 a b u s₁ s₂ t₁ t₂) (cm : IsColMinus c a b) {β δ γ : Fin G.maxDegree}
    (βb : c.IsFree b β) (hus₁ : c.col u s₁ = some β) (hus₂ : c.col u s₂ = some δ)
    (δa : c.IsFree a δ) (hst₁ : c.col s₁ t₁ = some γ) (hst₂ : c.col s₂ t₂ = some γ)
    (γa : c.IsFree a γ) (β₁ : c.IsFree t₁ β) (β₂ : c.IsFree t₂ β) (δ₁ : c.IsFree t₁ δ)
    (δ₂ : c.IsFree t₂ δ) (hR : ((unsetEdge c u s₂).kempeGraph β δ).Reachable u b) : False := by
  obtain ⟨hdis, -⟩ := cm.ab_facts hG
  have hγβ : γ ≠ β := fun e => hdis γ γa (e ▸ βb)
  have hδβ : δ ≠ β := fun e => hdis δ δa (e ▸ βb)
  have hδγ : δ ≠ γ := fun e => hd.ut₂ (c.col_proper (by rw [c.col_symm]; exact hus₂)
    (by rw [e]; exact hst₂))
  -- the chain of `s₁` in `G − ab − us₁` ends at `b`
  set ψ := unsetEdge c u s₁ with hψ
  set φ' := unsetEdge (unsetEdge c u s₂) u s₁ with hφ'
  have c2us₁ : (unsetEdge c u s₂).col u s₁ = some β := by
    rw [unsetEdge_col_of_ne c (not_pair (Or.inr hd.s₁s₂) (Or.inl hd.us₂))]; exact hus₁
  have f'uβ : φ'.IsFree u β := (isFree_unsetEdge_left _ hd.us₁ c2us₁ β).2 (Or.inl rfl)
  have f'uδ : φ'.IsFree u δ := (isFree_unsetEdge_left _ hd.us₁ c2us₁ δ).2
    (Or.inr ((isFree_unsetEdge_left c hd.us₂ hus₂ δ).2 (Or.inl rfl)))
  have hsub : ∀ p q, ((unsetEdge c u s₂).kempeGraph β δ).Adj p q →
      (φ'.kempeGraph β δ).Adj p q ∨ s(p, q) = s(u, s₁) := by
    rintro p q ⟨hne, hc⟩
    by_cases e : (p = u ∧ q = s₁) ∨ (p = s₁ ∧ q = u)
    · right
      rcases e with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rw [hp, hq]
      exact Sym2.eq_swap
    · left; exact ⟨hne, by rw [hφ', unsetEdge_col_of_ne _ e]; exact hc⟩
  have hsb' : (φ'.kempeGraph β δ).Reachable s₁ b := by
    rcases reach_split hsub hR with r | r
    · exact absurd (eq_of_reachable_of_free_both φ' f'uβ f'uδ r) hd.bu
    · exact r
  have hsb : (ψ.kempeGraph β δ).Reachable s₁ b := by
    refine reachable_mono_of_agree (fun p q hpq => ?_) hsb'
    by_cases e1 : (p = u ∧ q = s₁) ∨ (p = s₁ ∧ q = u)
    · exfalso
      have : φ'.col p q = none := by
        rcases e1 with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rw [hp, hq]
        · exact unsetEdge_col_self _ u s₁
        · rw [PEC.col_symm]; exact unsetEdge_col_self _ u s₁
      rw [this] at hpq
      rcases hpq with e | e <;> cases e
    by_cases e2 : (p = u ∧ q = s₂) ∨ (p = s₂ ∧ q = u)
    · exfalso
      have : φ'.col p q = none := by
        rw [hφ', unsetEdge_col_of_ne _ e1]
        rcases e2 with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rw [hp, hq]
        · exact unsetEdge_col_self c u s₂
        · rw [PEC.col_symm]; exact unsetEdge_col_self c u s₂
      rw [this] at hpq
      rcases hpq with e | e <;> cases e
    rw [hψ, unsetEdge_col_of_ne c e1, hφ', unsetEdge_col_of_ne _ e1, unsetEdge_col_of_ne c e2]
  -- facts in ψ
  have fψ : ∀ {w}, w ≠ u → w ≠ s₁ → ∀ ε, ψ.IsFree w ε ↔ c.IsFree w ε :=
    fun h1 h2 ε => isFree_unsetEdge_of_ne c h1 h2 ε
  have ψs₁β : ψ.IsFree s₁ β := (isFree_unsetEdge_right c hd.us₁ hus₁ β).2 (Or.inl rfl)
  have ψuβ : ψ.IsFree u β := (isFree_unsetEdge_left c hd.us₁ hus₁ β).2 (Or.inl rfl)
  have ψbβ : ψ.IsFree b β := (fψ hd.bu hd.bs₁ β).2 βb
  have ψaδ : ψ.IsFree a δ := (fψ hd.au hd.as₁ δ).2 δa
  have cψ : ∀ p q, ¬ ((p = u ∧ q = s₁) ∨ (p = s₁ ∧ q = u)) → ψ.col p q = c.col p q :=
    fun p q e => unsetEdge_col_of_ne c e
  have ψus₂ : ψ.col u s₂ = some δ := by
    rw [cψ u s₂ (not_pair (Or.inr hd.s₁s₂.symm) (Or.inl hd.us₁))]; exact hus₂
  have ψst₁ : ψ.col s₁ t₁ = some γ := by
    rw [cψ s₁ t₁ (not_pair (Or.inl hd.us₁.symm) (Or.inr hd.ut₁.symm))]; exact hst₁
  have ψst₂ : ψ.col s₂ t₂ = some γ := by
    rw [cψ s₂ t₂ (not_pair (Or.inl hd.us₂.symm) (Or.inl hd.s₁s₂.symm))]; exact hst₂
  have nu : ¬ (ψ.kempeGraph β δ).Reachable s₁ u := fun r =>
    not_three_linked ψ hd.bs₁.symm hd.us₁.symm hd.bu (Or.inl ψs₁β) (Or.inl ψbβ) (Or.inl ψuβ)
      hsb r
  have na : ¬ (ψ.kempeGraph β δ).Reachable s₁ a := fun r =>
    not_three_linked ψ hd.bs₁.symm hd.as₁.symm hd.ab.symm (Or.inl ψs₁β) (Or.inl ψbβ)
      (Or.inr ψaδ) hsb r
  -- φ₁: swap the `(β, δ)`-chain of `s₁`; φ₂: colour `ab` by `δ`
  set φ₁ := ψ.kempeSwap β δ s₁ with hφ₁
  have f1s₁δ : φ₁.IsFree s₁ δ := (kfree_flip₁ ψ (Reachable.refl s₁)).2 ψs₁β
  have f1bδ : φ₁.IsFree b δ := (kfree_flip₁ ψ hsb).2 ψbβ
  have f1aδ : φ₁.IsFree a δ := (kfree_off ψ na δ).2 ψaδ
  have f1uβ : φ₁.IsFree u β := (kfree_off ψ nu β).2 ψuβ
  have c1us₂ : φ₁.col u s₂ = some δ := kcol_keep ψ ψus₂ (Or.inr nu)
  have c1st₁ : φ₁.col s₁ t₁ = some γ := kcol_keep ψ ψst₁ (Or.inl ⟨hγβ, hδγ.symm⟩)
  have c1st₂ : φ₁.col s₂ t₂ = some γ := kcol_keep ψ ψst₂ (Or.inl ⟨hγβ, hδγ.symm⟩)
  have tfree : ∀ {t}, t ≠ u → t ≠ s₁ → c.IsFree t β → c.IsFree t δ →
      φ₁.IsFree t β ∧ φ₁.IsFree t δ := fun h1 h2 hb hδ' => by
    have hb' := (fψ h1 h2 β).2 hb
    have hδ'' := (fψ h1 h2 δ).2 hδ'
    have nt : ¬ (ψ.kempeGraph β δ).Reachable s₁ _ := fun r =>
      h2 (eq_of_reachable_of_free_both ψ hb' hδ'' r.symm).symm
    exact ⟨(kfree_off ψ nt β).2 hb', (kfree_off ψ nt δ).2 hδ''⟩
  obtain ⟨f1t₁β, f1t₁δ⟩ := tfree hd.ut₁.symm hd.s₁t₁.symm β₁ δ₁
  obtain ⟨f1t₂β, f1t₂δ⟩ := tfree hd.ut₂.symm hd.s₁t₂.symm β₂ δ₂
  set φ₂ := φ₁.setEdge δ cm.adj f1aδ f1bδ with hφ₂
  have off2 : ∀ p q, ¬ ((p = a ∧ q = b) ∨ (p = b ∧ q = a)) → φ₂.col p q = φ₁.col p q :=
    fun p q e => setEdge_col_off φ₁ cm.adj f1aδ f1bδ e
  have f2 : ∀ {w}, w ≠ a → w ≠ b → ∀ ε, φ₁.IsFree w ε → φ₂.IsFree w ε :=
    fun h1 h2 ε h => (isFree_setEdge_of_ne φ₁ δ cm.adj f1aδ f1bδ h1 h2 ε).2 h
  have hcm2 : IsColMinus φ₂ u s₁ := by
    refine ⟨c.col_adj hus₁, ?_, fun p q hpq hne => ?_⟩
    · rw [off2 u s₁ (not_pair (Or.inl hd.au.symm) (Or.inl hd.bu.symm)), hφ₁]
      exact kempeSwap_col_none ψ β δ s₁ (unsetEdge_col_self c u s₁)
    · by_cases e : (p = a ∧ q = b) ∨ (p = b ∧ q = a)
      · rw [hφ₂, setEdge_col, updFun, if_pos e]; exact Option.some_ne_none _
      rw [off2 p q e, hφ₁]
      refine extends_kempeSwap ψ β δ s₁ p q ?_
      have e' : ¬ ((p = u ∧ q = s₁) ∨ (p = s₁ ∧ q = u)) := by
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hne rfl
        · exact hne Sym2.eq_swap
      rw [cψ p q e']
      refine cm.total p q hpq fun he => e ?_
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
  have f2uβ := f2 hd.au.symm hd.bu.symm β f1uβ
  have f2s₁δ := f2 hd.as₁.symm hd.bs₁.symm δ f1s₁δ
  have f2t₁β := f2 hd.at₁.symm hd.bt₁.symm β f1t₁β
  have f2t₁δ := f2 hd.at₁.symm hd.bt₁.symm δ f1t₁δ
  have f2t₂β := f2 hd.at₂.symm hd.bt₂.symm β f1t₂β
  have f2t₂δ := f2 hd.at₂.symm hd.bt₂.symm δ f1t₂δ
  have c2us₂ : φ₂.col u s₂ = some δ := by
    rw [off2 u s₂ (not_pair (Or.inl hd.au.symm) (Or.inl hd.bu.symm))]; exact c1us₂
  have c2st₁ : φ₂.col s₁ t₁ = some γ := by
    rw [off2 s₁ t₁ (not_pair (Or.inl hd.as₁.symm) (Or.inl hd.bs₁.symm))]; exact c1st₁
  have c2st₂ : φ₂.col s₂ t₂ = some γ := by
    rw [off2 s₂ t₂ (not_pair (Or.inl hd.as₂.symm) (Or.inl hd.bs₂.symm))]; exact c1st₂
  by_cases r1 : (φ₂.kempeGraph β γ).Reachable u t₁
  · -- `t₂` is not `(β, γ)`-linked with `u`
    have r2 : ¬ (φ₂.kempeGraph β γ).Reachable u t₂ := fun r =>
      not_three_linked φ₂ hd.ut₁ hd.ut₂ hd.t₁t₂ (Or.inl f2uβ) (Or.inl f2t₁β) (Or.inl f2t₂β) r1 r
    set φ₃ := φ₂.kempeSwap β γ t₂ with hφ₃
    have cm3 : IsColMinus φ₃ u s₁ := hcm2.kempeSwap β γ t₂
    have f3uβ : φ₃.IsFree u β := (kfree_off φ₂ (fun r => r2 r.symm) β).2 f2uβ
    have f3s₁δ : φ₃.IsFree s₁ δ := (kfree_of_ne φ₂ hδβ hδγ).2 f2s₁δ
    have f3t₂δ : φ₃.IsFree t₂ δ := (kfree_of_ne φ₂ hδβ hδγ).2 f2t₂δ
    have c3us₂ : φ₃.col u s₂ = some δ := kcol_keep φ₂ c2us₂ (Or.inl ⟨hδβ, hδγ⟩)
    have c3st₂ : φ₃.col s₂ t₂ = some β := kcol_flip₂ φ₂ c2st₂
      (kempeGraph_adj_of_col (Or.inr (by rw [PEC.col_symm]; exact c2st₂))).reachable
    have link := fan2_link₀ hG cm3 c3us₂ f3s₁δ hd.s₁s₂ f3uβ f3s₁δ
    have rt : (φ₃.kempeGraph β δ).Reachable u t₂ :=
      reachable_of_col (reachable_of_col (Reachable.refl u) (Or.inr c3us₂)) (Or.inl c3st₂)
    exact not_three_linked φ₃ hd.us₁ hd.ut₂ hd.s₁t₂ (Or.inl f3uβ) (Or.inr f3s₁δ) (Or.inr f3t₂δ)
      link rt
  · -- `t₁` is not `(β, γ)`-linked with `u`: colour `G`
    set φ₃ := φ₂.kempeSwap β γ t₁ with hφ₃
    have cm3 : IsColMinus φ₃ u s₁ := hcm2.kempeSwap β γ t₁
    have f3uβ : φ₃.IsFree u β := (kfree_off φ₂ (fun r => r1 r.symm) β).2 f2uβ
    have f3s₁δ : φ₃.IsFree s₁ δ := (kfree_of_ne φ₂ hδβ hδγ).2 f2s₁δ
    have f3t₁δ : φ₃.IsFree t₁ δ := (kfree_of_ne φ₂ hδβ hδγ).2 f2t₁δ
    have c3st₁ : φ₃.col s₁ t₁ = some β := kcol_flip₂ φ₂ c2st₁
      (kempeGraph_adj_of_col (Or.inr (by rw [PEC.col_symm]; exact c2st₁))).reachable
    set φ₄ := unsetEdge φ₃ s₁ t₁ with hφ₄
    have f4s₁δ : φ₄.IsFree s₁ δ := (isFree_unsetEdge_left φ₃ hd.s₁t₁ c3st₁ δ).2 (Or.inr f3s₁δ)
    have f4s₁β : φ₄.IsFree s₁ β := (isFree_unsetEdge_left φ₃ hd.s₁t₁ c3st₁ β).2 (Or.inl rfl)
    have f4t₁δ : φ₄.IsFree t₁ δ := (isFree_unsetEdge_right φ₃ hd.s₁t₁ c3st₁ δ).2 (Or.inr f3t₁δ)
    have hadj : G.Adj s₁ t₁ := c.col_adj hst₁
    set φ₅ := φ₄.setEdge δ hadj f4s₁δ f4t₁δ with hφ₅
    have f5s₁β : φ₅.IsFree s₁ β :=
      setEdge_isFree_left φ₄ hadj f4s₁δ f4t₁δ hδβ.symm (fun x _ => f4s₁β x)
    have f5uβ : φ₅.IsFree u β := (isFree_setEdge_of_ne φ₄ δ hadj f4s₁δ f4t₁δ hd.us₁ hd.ut₁ β).2
      ((isFree_unsetEdge_of_ne φ₃ hd.us₁ hd.ut₁ β).2 f3uβ)
    have hcm5 : IsColMinus φ₅ u s₁ := cm3.extends_of (extends_unset_set hadj f4s₁δ f4t₁δ) (by
      rw [hφ₅, setEdge_col_off φ₄ hadj f4s₁δ f4t₁δ (not_pair (Or.inl hd.us₁) (Or.inl hd.ut₁)),
        hφ₄, unsetEdge_col_of_ne φ₃ (not_pair (Or.inl hd.us₁) (Or.inl hd.ut₁))]
      exact cm3.uncol)
    exact close_uncol hG hcm5 f5uβ f5s₁β

end Overfull
