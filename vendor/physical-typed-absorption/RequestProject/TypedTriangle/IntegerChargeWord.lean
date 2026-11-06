/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ChargeWordPolarization
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
namespace TypedTriangle.ChargePolar
variable {V : Type*} [Fintype V]

lemma signedWord_append (l m : List (Bool × Sym2 V)) :
    signedWord (l++m) = signedWord l+signedWord m := by
  induction l with
  | nil => simp [signedWord]
  | cons z l ih => simp only [List.cons_append,signedWord,ih]; abel

lemma signedWord_replicate (n : ℕ) (z : Bool × Sym2 V) :
    signedWord (List.replicate n z) = (n:ℤ) • (if z.1 then ind {z.2} else -ind {z.2}) := by
  induction n with
  | zero => simp [signedWord]
  | succ n ih =>
    simp only [List.replicate_succ,signedWord,ih,Nat.cast_add,Nat.cast_one,add_smul,one_smul]
    abel

def letters (c : ℤ) (e : Sym2 V) : List (Bool × Sym2 V) :=
  List.replicate c.natAbs (decide (0≤c),e)

lemma signedWord_letters (c : ℤ) (e : Sym2 V) :
    signedWord (letters c e) = c • ind {e} := by
  rw [letters,signedWord_replicate]
  by_cases hc : 0≤c
  · simp [hc,Int.natCast_natAbs,abs_of_nonneg hc]
  · simp [hc,Int.natCast_natAbs,abs_of_neg (by omega : c<0)]

lemma letters_length (c : ℤ) (e : Sym2 V) : (letters c e).length = c.natAbs := by
  simp [letters]

lemma mem_letters {c : ℤ} {e : Sym2 V} {z : Bool × Sym2 V}
    (hz : z ∈ letters c e) : z.2=e ∧ c≠0 := by
  obtain ⟨hn,rfl⟩ := List.mem_replicate.mp hz
  exact ⟨rfl,by intro h; simp [h] at hn⟩

theorem word_on_finset (s : Finset (Sym2 V)) (x : Sym2 V → ℤ) :
    ∃ l : List (Bool × Sym2 V),
      signedWord l = ∑ e ∈ s, x e • ind {e} ∧
      l.length = ∑ e ∈ s, (x e).natAbs ∧
      ∀ z ∈ l, z.2∈s ∧ x z.2≠0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨[],by simp [signedWord],by simp,by simp⟩
  | @insert e s hes ih =>
    obtain ⟨l,hl,hlen,hmem⟩ := ih
    refine ⟨letters (x e) e ++ l,?_,?_,?_⟩
    · rw [signedWord_append,signedWord_letters,hl,sum_insert hes]
    · rw [List.length_append,letters_length,hlen,sum_insert hes]
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · obtain ⟨he,hn⟩ := mem_letters hz
        exact ⟨by simp [he],by simpa only [he] using hn⟩
      · obtain ⟨hs,hn⟩ := hmem z hz
        exact ⟨mem_insert_of_mem hs,hn⟩

/-- Every integer edge vector has a signed word of EXACT l1 length.
No certificate and no bound on homogeneous classes are inputs. -/
theorem integer_word (x : Sym2 V → ℤ) :
    ∃ l : List (Bool × Sym2 V), signedWord l=x ∧
      (l.length:ℤ)=∑ e, |x e| ∧ ∀ z ∈ l, x z.2≠0 := by
  obtain ⟨l,hl,hlen,hmem⟩ := word_on_finset univ x
  have hsum : (∑ e : Sym2 V, x e • ind {e})=x := by
    funext f
    simp [Finset.sum_apply,Pi.smul_apply,ind,eq_comm]
  refine ⟨l,hl.trans hsum,?_,fun z hz => (hmem z hz).2⟩
  rw [hlen,Nat.cast_sum]
  exact sum_congr rfl fun e _ => Int.natCast_natAbs _

end TypedTriangle.ChargePolar
