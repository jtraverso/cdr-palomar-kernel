/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# CDR Paper III: prescribed block types and abundance

Four independent statements, using only Mathlib on the statement side:
exact interior type counts with sparse completion, the optimal leading
counting coefficient 1/6, arbitrarily many distinct Pasch counts with the
same exact type matrix, and eventual existence for each fixed k >= 4.

The arithmetic threshold in the last statement is ineffective. The count
theorem controls the leading n^2 log n term, not a second-order term.
Pasch diversity does not prescribe arbitrary Pasch values. The intentional
holes here are absent from the proved Solution and its import closure.
-/

@[expose] public section
open Finset Classical
noncomputable section

namespace TypedTriangle
structure Host (V I : Type*) where
  G : SimpleGraph V
  lab : V → I

variable {V I : Type*} [Fintype V]

def triEdges (T : Finset V) : Finset (Sym2 V) := T.sym2.filter (fun e => ¬ e.IsDiag)

def edges (H : Host V I) : Finset (Sym2 V) := univ.filter (fun e => e ∈ H.G.edgeSet)

def IsAllowed (H : Host V I) (F : Set (Multiset I)) (T : Finset V) : Prop :=
  T.card = 3 ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → H.G.Adj x y) ∧ T.val.map H.lab ∈ F

def IsDecomposition (H : Host V I) (F : Set (Multiset I)) (J : Finset (Sym2 V))
    (D : Finset (Finset V)) : Prop :=
  (∀ T ∈ D, IsAllowed H F T) ∧ (D : Set (Finset V)).PairwiseDisjoint triEdges ∧
    D.biUnion triEdges = J

end TypedTriangle

namespace STS
variable {α : Type*} [DecidableEq α]

def IsSTS (B : Finset (Finset α)) : Prop :=
  (∀ A ∈ B, A.card = 3) ∧ ∀ x y : α, x ≠ y → ∃! A, A ∈ B ∧ x ∈ A ∧ y ∈ A

end STS

namespace CDRBicolour.Absorption
variable {V : Type*} [Fintype V] [DecidableEq V]

def nbL (L : Finset (Sym2 V)) (p : V) : Finset V := univ.filter fun w => s(w, p) ∈ L

def degL (L : Finset (Sym2 V)) (p : V) : ℕ := #(nbL L p)

end CDRBicolour.Absorption

namespace CDRBicolour.KBicolor
open TypedTriangle
variable {k n : ℕ}

def bicF (k : ℕ) : Set (Multiset (Fin k)) := {m | Multiset.card m = 3 ∧ m.toFinset.card = 2}

abbrev kHost {V : Type*} (lab : V → Fin k) : Host V (Fin k) := ⟨⊤, lab⟩

def ksz {V : Type*} [Fintype V] (lab : V → Fin k) (X : Fin k) : ℕ :=
  (univ.filter fun v => lab v = X).card

def kTypeCount {V : Type*} (lab : V → Fin k) (D : Finset (Finset V)) (X Y : Fin k) : ℕ :=
  #(D.filter fun T => T.val.map lab = {X, X, Y})

def kBlocks (lab : Fin n → Fin k) : Finset (Finset (Finset (Fin n))) :=
  univ.filter fun X => _root_.STS.IsSTS X ∧ ∀ B ∈ X, (B.image lab).card = 2

end CDRBicolour.KBicolor

namespace CDRBicolour.KBicolor
variable {n k : ℕ}

abbrev TypeCoord (k : ℕ) := ↥((univ : Finset (Fin k)).offDiag)

def typeVector (lab : Fin n → Fin k) (D : Finset (Finset (Fin n))) : TypeCoord k → ℕ :=
  fun p => kTypeCount lab D p.1.1 p.1.2

def exactTypeFibre (lab : Fin n → Fin k) (t : TypeCoord k → ℕ) :
    Finset (Finset (Finset (Fin n))) := (kBlocks lab).filter (fun D => typeVector lab D = t)

def exactTypeCount (lab : Fin n → Fin k) (t : TypeCoord k → ℕ) : ℕ := #(exactTypeFibre lab t)

end CDRBicolour.KBicolor

namespace TypedTriangle.Pasch

def IsPasch {V : Type*} [DecidableEq V] (S : Finset (Finset V)) : Prop :=
  S.card = 4 ∧ (∀ T ∈ S, T.card = 3) ∧ (S.biUnion id).card = 6 ∧
    (∀ v ∈ S.biUnion id, (S.filter (fun T => v ∈ T)).card = 2) ∧
      (S : Set (Finset V)).Pairwise (fun A B => (A ∩ B).card ≤ 1)

/-- An explicit instance expression avoids generated tactic proof names. -/
instance decidableIsPasch {V : Type*} [DecidableEq V] (S : Finset (Finset V)) :
    Decidable (IsPasch S) :=
  id (inferInstance : Decidable (S.card = 4 ∧ (∀ T ∈ S, T.card = 3) ∧
    (S.biUnion id).card = 6 ∧
    (∀ v ∈ S.biUnion id, (S.filter (fun T => v ∈ T)).card = 2) ∧
    (S : Set (Finset V)).Pairwise (fun A B => (A ∩ B).card ≤ 1)))

def configurations {V : Type*} [DecidableEq V] (D : Finset (Finset V)) : Finset (Finset (Finset V)) :=
  (D.powersetCard 4).filter IsPasch

def count {V : Type*} [DecidableEq V] (D : Finset (Finset V)) : ℕ := (configurations D).card

end TypedTriangle.Pasch

namespace CDRBicolour.PaperIII

def IsSTS {v : ℕ} (B : Finset (Finset (Fin v))) : Prop :=
  (∀ b ∈ B, b.card = 3) ∧ ∀ x y : Fin v, x ≠ y → ∃! b, b ∈ B ∧ x ∈ b ∧ y ∈ b

def IsBicolouring {v m : ℕ} (B : Finset (Finset (Fin v))) (col : Fin v → Fin m) : Prop :=
  Function.Surjective col ∧ ∀ b ∈ B, (b.image col).card = 2

def Bicolourable (v m : ℕ) : Prop :=
  ∃ (B : Finset (Finset (Fin v))) (col : Fin v → Fin m), IsSTS B ∧ IsBicolouring B col

def Admissible (v : ℕ) : Prop := v % 6 = 1 ∨ v % 6 = 3

end CDRBicolour.PaperIII

namespace CDRBicolour.KBicolor
open TypedTriangle CDRBicolour.Absorption

theorem kbicolour_completion_types_exact (k : ℕ) (hk : 3 ≤ k) {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ X, δ * n ≤ ksz lab X) →
      (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X - 1) = n * (n - 1) →
      ∀ t : Fin k → Fin k → ℕ,
      (∀ X Y, X ≠ Y → 2 * (t X Y + t Y X) = ksz lab X * ksz lab Y) →
      (∀ X, 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y = ksz lab X * (ksz lab X - 1)) →
      (∀ X Y, X ≠ Y → ε * (n : ℝ) ^ 2 ≤ t X Y) →
      ∀ (Q : Finset (Finset (Fin n))) (ΔQ : ℕ),
      (∀ T ∈ Q, IsAllowed (kHost lab) (bicF k) T) →
      (Q : Set (Finset (Fin n))).PairwiseDisjoint triEdges →
      (∀ p, degL (Q.biUnion triEdges) p ≤ ΔQ) → (ΔQ : ℝ) ≤ γ * n →
      ∃ D : Finset (Finset (Fin n)), IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D ∧
        Q ⊆ D ∧ ∀ X Y, X ≠ Y → kTypeCount lab D X Y = t X Y := by
  sorry

theorem optimal_prescribed_type_count_of_three_le (k : ℕ) (hk : 3 ≤ k) {δ ζ ε : ℝ}
    (hδ : 0 < δ) (hζ : 0 < ζ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ i, δ*n ≤ ksz lab i) →
      (∀ i j, i ≠ j → Even (ksz lab i*ksz lab j)) →
      3*∑ i,ksz lab i*(ksz lab i-1)=n*(n-1) →
      ∀ target : Fin k → Fin k → ℕ,
      (∀ i j, i ≠ j → 2*(target i j+target j i)=ksz lab i*ksz lab j) →
      (∀ i, 2*∑ j ∈ univ.filter (fun j => j ≠ i), target i j=ksz lab i*(ksz lab i-1)) →
      (∀ i j, i ≠ j → ζ*(n : ℝ)^2 ≤ target i j) →
      let tv : TypeCoord k → ℕ := fun q => target q.1.1 q.1.2
      0 < exactTypeCount lab tv ∧
        (1/6-ε)*(n : ℝ)^2*Real.log n ≤ Real.log (exactTypeCount lab tv) ∧
        Real.log (exactTypeCount lab tv) ≤ (1/6+ε)*(n : ℝ)^2*Real.log n := by
  sorry

theorem kbicolour_types_exact_many_pasch_counts (K k : ℕ) (hk : 3 ≤ k) {δ η : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ X, δ*n ≤ ksz lab X) →
      (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X-1) = n*(n-1) →
      ∀ t : Fin k → Fin k → ℕ,
      (∀ X Y, X ≠ Y → 2*(t X Y+t Y X) = ksz lab X * ksz lab Y) →
      (∀ X, 2*∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y = ksz lab X * (ksz lab X-1)) →
      (∀ X Y, X ≠ Y → η*ksz lab X*ksz lab Y ≤ 2*t X Y) →
      ∃ D : Fin K → Finset (Finset (Fin n)),
        (∀ i, IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) (D i)) ∧
        (∀ i X Y, X ≠ Y → kTypeCount lab (D i) X Y = t X Y) ∧
        Function.Injective (fun i => Pasch.count (D i)) := by
  sorry

end CDRBicolour.KBicolor

namespace CDRBicolour.PaperIII

theorem bicolourable_eventually_unconditional {k : ℕ} (hk : 4 ≤ k) :
    ∃ v₀ : ℕ, ∀ v, v₀ ≤ v → Admissible v → Bicolourable v k := by
  sorry

end CDRBicolour.PaperIII
