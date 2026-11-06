module
public import RequestProject.TypedTriangle.PaschRichBankHistory
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch.RichBank
open S07V40
variable {V I Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]

/-- Intermediate rich supply. The native constructor below supplies the cell,
its actual two modes and its potential certificate in one existential. -/
def CellSupply (H : Host V I) (F : Set (Multiset I)) (S : MacroSetting V Q C)
    (Ub : ℕ) (pay : ℝ) : Prop :=
  ∀ (B : Finset (Sym2 V)) (Z : Finset V), (∀ v, deg B v ≤ S.q+S.Bstar*S.E) →
    Z.card ≤ S.zmax → ∀ (R : Finset (Finset V)), PairCodegreeBound R 2 →
    (∀ T ∈ R, triEdges T ⊆ B) → ∀ l : Lab C S.P, S.g l.2.1 ∈ S.K Z →
    ∀ r : ℕ, ∃ e : Entry V C S.P, GoodEntry H F S Ub pay e ∧
      e.round=r ∧ e.lab=l ∧ e.used=B ∧ e.deleted=Z ∧ e.previous=R

theorem place_round {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} (hSupply : CellSupply H F S Ub pay)
    (Z : Finset V) (hZ : Z.card ≤ S.zmax) (r : ℕ) :
    ∀ (ls : List (Lab C S.P)) (es : List (Entry V C S.P)), ValidHistory H F S Ub pay es →
      (∀ l ∈ ls, S.g l.2.1 ∈ S.K Z) →
      (∀ v, v ∉ Z → deg (usedEdges es) v+ls.length*S.E < S.q+S.Bstar*S.E) →
      (∀ v ∈ Z, deg (usedEdges es) v < S.q+S.Bstar*S.E) →
      ∃ added : List (Entry V C S.P), ValidHistory H F S Ub pay (added++es) ∧
        added.map Entry.lab = ls.reverse ∧
        (∀ e ∈ added, e.round=r ∧ e.deleted=Z) ∧
        (∀ v, v ∉ Z → deg (usedEdges (added++es)) v ≤ deg (usedEdges es) v+ls.length*S.E) ∧
        (∀ v ∈ Z, deg (usedEdges (added++es)) v = deg (usedEdges es) v) ∧
        (usedEdges (added++es)).card ≤ (usedEdges es).card+ls.length*S.E := by
  intro ls
  induction ls with
  | nil =>
    intro es hHist hActive hout hin
    exact ⟨[], hHist, rfl, by simp, by simp, by simp, by simp⟩
  | cons l ls ih =>
    intro es hHist hActive hout hin
    have hMax : ∀ v, deg (usedEdges es) v ≤ S.q+S.Bstar*S.E := by
      intro v
      by_cases hv : v ∈ Z
      · exact (hin v hv).le
      · have hh := hout v hv
        omega
    obtain ⟨e, he, her, hel, heB, heZ, heR⟩ := hSupply (usedEdges es) Z hMax hZ
      (modes es) hHist.codegree hHist.modes_edges l (hActive l (by simp)) r
    have hNew := hHist.cons e he heB heR
    have hSize := he.good.2.2.2.2.2.1
    have hAvoid := he.good.2.2.2.2.1
    have hDeg (v : V) : deg (usedEdges (e::es)) v ≤ deg (usedEdges es) v+S.E := by
      change deg (e.cell.tot∪usedEdges es) v ≤ _
      rw [union_comm]
      exact (deg_union_le _ _ v).trans (Nat.add_le_add_left hSize _)
    have hSame (v : V) (hv : v ∈ Z) : deg (usedEdges (e::es)) v = deg (usedEdges es) v := by
      change deg (e.cell.tot∪usedEdges es) v = _
      rw [union_comm]
      exact deg_union_of_avoids (by simpa only [heZ] using hAvoid) hv
    have hOut : ∀ v, v ∉ Z → deg (usedEdges (e::es)) v+ls.length*S.E < S.q+S.Bstar*S.E := by
      intro v hv
      have hh := hout v hv
      have hd := hDeg v
      simp only [List.length_cons, add_mul, one_mul] at hh
      omega
    obtain ⟨added, hFinal, hLabs, hRounds, hOutFinal, hInFinal, hCard⟩ :=
      ih (e::es) hNew (fun l hl => hActive l (List.mem_cons_of_mem _ hl)) hOut
        (fun v hv => by rw [hSame v hv]; exact hin v hv)
    have hEq : (added++[e])++es = added++(e::es) := by simp only [List.append_assoc, List.singleton_append]
    refine ⟨added++[e], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hEq] using hFinal
    · simp only [List.map_append, List.map_cons, List.map_nil, hLabs, hel, List.reverse_cons]
    · intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hRounds f hf
      · obtain rfl := List.mem_singleton.mp hf
        exact ⟨her, heZ⟩
    · intro v hv
      rw [hEq]
      have hf := hOutFinal v hv
      have hd := hDeg v
      simp only [List.length_cons, add_mul, one_mul]
      omega
    · intro v hv
      rw [hEq, hInFinal v hv, hSame v hv]
    · rw [hEq]
      have hc : (usedEdges (e::es)).card ≤ (usedEdges es).card+S.E := by
        exact (card_union_le _ _).trans (by omega)
      simp only [List.length_cons, add_mul, one_mul]
      omega

end TypedTriangle.Pasch.RichBank

#print axioms TypedTriangle.Pasch.RichBank.place_round
