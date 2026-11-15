/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.GroupLatinIntercalates
public import CDRIIILib.KBicolor.TwoTorsionProducts
public import CDRIIILib.KBicolor.LatinIntercalateTransport

/-! # Same-order Latin tables with explicitly separated intercalate counts -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical TypedTriangle.Applications.Latin

def dyadicSquare (r i : ℕ) (hi : 2*i ≤ r) : LatinSquare (Fin (2^r)) :=
  transportSquare (Fintype.equivOfCardEq (by simpa using dyadicLatinGroup_card hi))
    (LatinSquare.add (DyadicLatinGroup r i))

theorem dyadicSquare_count (r i : ℕ) (hi : 2*i ≤ r) :
    4 * (intercalates (dyadicSquare r i hi)).card = (2^r)^2*(2^(r-i)-1) := by
  have ht : (twoTorsion (DyadicLatinGroup r i)).card = 2^(r-i) := by
    calc
      _ = Fintype.card (TwoTorsionElement (DyadicLatinGroup r i)) :=
        by
          have hh := (Fintype.card_subtype (fun a : DyadicLatinGroup r i => a+a=0)).symm
          convert hh using 1
          · congr 1
            ext x
            simp only [twoTorsion, mem_filter, mem_univ, true_and]
      _ = _ := dyadicLatinGroup_two_torsion hi
  calc
    _ = 4 * (intercalates (LatinSquare.add (DyadicLatinGroup r i))).card := by
      unfold dyadicSquare
      rw [intercalates_card_transport]
    _ = Fintype.card (DyadicLatinGroup r i)^2 * ((twoTorsion (DyadicLatinGroup r i)).card-1) :=
      four_mul_group_intercalates
    _ = _ := by rw [dyadicLatinGroup_card hi, ht]

theorem dyadicSquare_count_real (r i : ℕ) (hi : 2*i ≤ r) :
    4 * ((intercalates (dyadicSquare r i hi)).card : ℝ) =
      ((2:ℝ)^r)^2 * ((2:ℝ)^(r-i)-1) := by
  have hh := dyadicSquare_count r i hi
  have hp : 1 ≤ 2^(r-i) := Nat.one_le_pow _ _ (by norm_num)
  exact_mod_cast hh

theorem dyadicSquare_gap {K r : ℕ} (hr : 2*K ≤ r) (i j : Fin K) (hij : i < j) :
    ((2:ℝ)^r)^3 / (4*(2:ℝ)^K) ≤
      (intercalates (dyadicSquare r i (by omega))).card -
        ((intercalates (dyadicSquare r j (by omega))).card : ℝ) := by
  have hi := dyadicSquare_count_real r i (by omega)
  have hj := dyadicSquare_count_real r j (by omega)
  have hp : (2:ℝ)^(r-j.val+1) ≤ 2^(r-i.val) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ] at hp
  have hprod : (2:ℝ)^(r-j.val)*2^j.val = 2^r := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have hK : (2:ℝ)^j.val ≤ 2^K := pow_le_pow_right₀ (by norm_num) (by omega)
  have hscale : (2:ℝ)^r ≤ 2^K * 2^(r-j.val) := by
    nlinarith [mul_le_mul_of_nonneg_left hK (show (0:ℝ)≤2^(r-j.val) by positivity)]
  apply (div_le_iff₀ (show (0:ℝ)<4*2^K by positivity)).mpr
  have hsq : (0:ℝ)≤((2:ℝ)^r)^2 := sq_nonneg _
  have hdiff := mul_le_mul_of_nonneg_left hp hsq
  have hscale' := mul_le_mul_of_nonneg_left hscale hsq
  have hI : ((2:ℝ)^r)^2 * 2^(r-j.val) ≤
      4*((intercalates (dyadicSquare r i (by omega))).card -
        ((intercalates (dyadicSquare r j (by omega))).card : ℝ)) := by
    nlinarith only [hi,hj,hdiff]
  have hIscale := mul_le_mul_of_nonneg_left hI (show (0:ℝ)≤2^K by positivity)
  nlinarith only [hIscale,hscale']


end CDRBicolour.KBicolor.LatinPasch
