/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.PieceGeometry
public import CDRIIILib.KBicolor.Wilson.OptimizedLocalSeed
public import CDRBicolour.Absorption.Count.Wilson.GlobalSeed

/-!
# Transport and sum of local seeds on the actual Wilson pieces

The pieces are subtypes of the original vertex set. Their common reserve is
shared, not duplicated in the host. The generic push-forward already used in
the three-colour construction transports the local seeds.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined
open CDRBicolour.Absorption.Count.Wilson (push push_map push_eq_zero sum_push mem_triEdges_map_iff mem_tE)
open scoped Classical

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}
variable (h : Setup lab κ g t) {S : Finset (Finset (Fin g))}

abbrev Piece (i : Fin g) := {u : Fin n // u ∈ piece h i}

def pieceEmb (i : Fin g) : Piece h i ↪ Fin n := ⟨Subtype.val, Subtype.val_injective⟩

def pieceLab (i : Fin g) (u : Piece h i) : Fin k := lab u.val

def pieceReserve (i : Fin g) : Finset (Piece h i) := univ.filter fun u => u.val ∈ reserve h

theorem map_piece_allowed (hS : _root_.STS.IsSTS S) (Λ : LFam A S t)
    (i : Fin g) (T : Finset (Piece h i)) :
    T.map (pieceEmb h i) ∈ allowed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) ↔
      T ∈ triG (pieceLab h i) (bicF k) := by
  have hmem : T.map (pieceEmb h i) ∈ allowed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) ↔
      IsAllowed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) (T.map (pieceEmb h i)) := by
    simp only [allowed, mem_filter, mem_univ, true_and]
  rw [hmem, gmem_tri]
  have hcol : (T.map (pieceEmb h i)).val.map lab = T.val.map (pieceLab h i) := by
    rw [map_val, Multiset.map_map]
    rfl
  constructor
  · rintro ⟨h3,-,hF⟩
    refine ⟨by rwa [card_map] at h3, fun x _ y _ hxy => by simpa [cHostG] using hxy, ?_⟩
    change T.val.map (pieceLab h i) ∈ bicF k
    rwa [← hcol]
  · rintro ⟨h3,-,hF⟩
    refine ⟨by rwa [card_map], ?_, ?_⟩
    · intro u hu v hv huv
      obtain ⟨u',-,rfl⟩ := mem_map.mp hu
      obtain ⟨v',-,rfl⟩ := mem_map.mp hv
      exact piece_complete h hS Λ i u'.property v'.property huv
    · change (T.map (pieceEmb h i)).val.map lab ∈ bicF k
      rwa [hcol]

def assembledSeed (φ : ∀ i : Fin g, Finset (Piece h i) → ℝ) (T : Finset (Fin n)) : ℝ :=
  ∑ i, CDRBicolour.Absorption.Count.Wilson.push (pieceEmb h i) (φ i) T

theorem piece_seed_bounds (hS : _root_.STS.IsSTS S) (Λ : LFam A S t)
    {φ : ∀ i : Fin g, Finset (Piece h i) → ℝ} {lo hi : ℝ} (hlo : 0 ≤ lo)
    (hφ : ∀ i T, T ∈ triG (pieceLab h i) (bicF k) → lo ≤ φ i T ∧ φ i T ≤ hi)
    (i : Fin g) {T : Finset (Fin n)}
    (hT : IsAllowed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) T) :
    0 ≤ CDRBicolour.Absorption.Count.Wilson.push (pieceEmb h i) (φ i) T ∧ CDRBicolour.Absorption.Count.Wilson.push (pieceEmb h i) (φ i) T ≤ max hi 0 := by
  by_cases hex : ∃ T' : Finset (Piece h i), T'.map (pieceEmb h i) = T
  · obtain ⟨T',rfl⟩ := hex
    rw [push_map]
    have hmem : T'.map (pieceEmb h i) ∈ allowed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) := by
      simp only [allowed, mem_filter, mem_univ, true_and]
      exact hT
    have hb := hφ i T' ((map_piece_allowed h hS Λ i T').mp hmem)
    exact ⟨hlo.trans hb.1, hb.2.trans (le_max_left _ _)⟩
  · push_neg at hex
    rw [push_eq_zero _ _ hex]
    exact ⟨le_rfl,le_max_right _ _⟩

theorem piece_seed_edge_sum (hS : _root_.STS.IsSTS S) (Λ : LFam A S t)
    {φ : ∀ i : Fin g, Finset (Piece h i) → ℝ}
    (hM : ∀ i, MincG (pieceLab h i) (bicF k) (φ i) =
      fun e : E0 (Piece h i) => reserveTarget (pieceReserve h i) (g : ℝ) e.1)
    (i : Fin g) {u v : Fin n} (huv : u ≠ v) :
    (∑ T ∈ (allowed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k)).filter
        (fun T => s(u,v) ∈ triEdges T), CDRBicolour.Absorption.Count.Wilson.push (pieceEmb h i) (φ i) T) =
      if u ∈ piece h i ∧ v ∈ piece h i then
        (if u ∈ reserve h ∧ v ∈ reserve h then 1/(g : ℝ) else 1) else 0 := by
  rw [sum_push]
  by_cases hp : u ∈ piece h i ∧ v ∈ piece h i
  · rw [ite_eq_left hp]
    let u' : Piece h i := ⟨u,hp.1⟩
    let v' : Piece h i := ⟨v,hp.2⟩
    have huv' : u' ≠ v' := fun he => huv (congrArg Subtype.val he)
    have heq := congrFun (hM i) ⟨s(u',v'), fun hd => huv' (Sym2.mk_isDiag_iff.mp hd)⟩
    change (∑ T ∈ (triG (pieceLab h i) (bicF k)).filter
      (fun T => s(u',v') ∈ triEdges T), φ i T) = _ at heq
    have htarget : reserveTarget (pieceReserve h i) (g : ℝ) s(u',v') =
        if u ∈ reserve h ∧ v ∈ reserve h then 1/(g : ℝ) else 1 := by
      simp only [reserveTarget, Sym2.lift_mk, pieceReserve, mem_filter, mem_univ, true_and]
      rfl
    rw [htarget] at heq
    rw [← heq]
    apply sum_congr ?_ (fun _ _ => rfl)
    ext T
    have hedge : s(u,v) ∈ triEdges (T.map (pieceEmb h i)) ↔ s(u',v') ∈ triEdges T :=
      CDRBicolour.Absorption.Count.Wilson.mem_triEdges_map_iff (pieceEmb h i) T u' v'
    simp only [mem_filter,mem_univ,true_and,map_piece_allowed h hS Λ,hedge]
  · rw [ite_eq_right hp]
    apply sum_eq_zero
    intro T hT
    exfalso
    have hedge := (mem_filter.mp (mem_filter.mp hT).2).2
    obtain ⟨hu,hv,-⟩ := mem_tE.mp hedge
    obtain ⟨u',-,hu'⟩ := mem_map.mp hu
    obtain ⟨v',-,hv'⟩ := mem_map.mp hv
    exact hp ⟨hu' ▸ u'.property,hv' ▸ v'.property⟩

/-- The local exact seeds give H1 for the actual common Wilson residual. -/
theorem global_seed_of_local (hS : _root_.STS.IsSTS S) (Λ : LFam A S t) (hg : 0 < g)
    {φ : ∀ i : Fin g, Finset (Piece h i) → ℝ} {lo hi C : ℝ} (hlo : 0 ≤ lo)
    (hφ : ∀ i T, T ∈ triG (pieceLab h i) (bicF k) → lo ≤ φ i T ∧ φ i T ≤ hi)
    (hM : ∀ i, MincG (pieceLab h i) (bicF k) (φ i) =
      fun e : E0 (Piece h i) => reserveTarget (pieceReserve h i) (g : ℝ) e.1)
    (hC1 : 1/(C*(n : ℝ)) ≤ lo) (hC2 : (g : ℝ)*max hi 0 ≤ C/n) :
    IsDiffuseSeed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) C (assembledSeed h φ) := by
  refine ⟨fun T hT => ?_, fun e he => ?_⟩
  · rw [Fintype.card_fin]
    obtain ⟨i0,hi0⟩ := residual_clique_piece h hS Λ hg hT.2.1
    let T' : Finset (Piece h i0) := univ.filter fun u => u.val ∈ T
    have hTT : T'.map (pieceEmb h i0) = T := by
      ext u
      simp only [mem_map, T', mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨u',hu',rfl⟩; exact hu'
      · intro hu; exact ⟨⟨u,hi0 hu⟩,hu,rfl⟩
    have hb := fun i => piece_seed_bounds h hS Λ hlo hφ i hT
    constructor
    · calc
        _ ≤ lo := hC1
        _ ≤ CDRBicolour.Absorption.Count.Wilson.push (pieceEmb h i0) (φ i0) T := by
          rw [← hTT,push_map]
          apply (hφ i0 T' _).1
          apply (map_piece_allowed h hS Λ i0 T').mp
          rw [hTT]
          simpa only [allowed,mem_filter,mem_univ,true_and] using hT
        _ ≤ assembledSeed h φ T := by
          exact single_le_sum (fun i _ => (hb i).1) (mem_univ i0)
    · calc
        _ ≤ ∑ _i : Fin g, max hi 0 := sum_le_sum fun i _ => (hb i).2
        _ = (g : ℝ)*max hi 0 := by simp
        _ ≤ _ := hC2
  · induction e using Sym2.ind with
    | _ u v =>
    have hadj : (rG ((crossP h Λ).biUnion triEdges)).Adj u v := he
    have huv : u ≠ v := hadj.ne
    unfold assembledSeed
    rw [sum_comm]
    refine (sum_congr rfl (fun i _ => by convert piece_seed_edge_sum h hS Λ hM i huv using 3)).trans ?_
    by_cases hRR : u ∈ reserve h ∧ v ∈ reserve h
    · have hp : ∀ i : Fin g, u ∈ piece h i ∧ v ∈ piece h i := fun _ =>
        ⟨mem_union.mpr (Or.inr hRR.1),mem_union.mpr (Or.inr hRR.2)⟩
      simp only [hRR,hp,and_self,ite_true,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
      have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
      field_simp
    · obtain ⟨i0,hi0⟩ := residual_edge_unique_piece h hS Λ hadj hRR
      simp only [ite_eq_right hRR]
      simp_rw [hi0]
      simp

end CDRBicolour.KBicolor.Wilson
