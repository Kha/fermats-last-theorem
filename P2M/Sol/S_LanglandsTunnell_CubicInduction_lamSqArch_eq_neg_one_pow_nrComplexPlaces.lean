import Definitions.Def_LanglandsTunnell_LambdaSquared
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import P2M.Util
namespace P2MW.S_LanglandsTunnell_CubicInduction_lamSqArch_eq_neg_one_pow_nrComplexPlaces

set_option autoImplicit false

open NumberField

theorem solution
    (K : Type) [Field K] [NumberField K] :
    LanglandsTunnell.CubicInduction.lamSqArch K = (-1 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
  classical
  have hiff : LanglandsTunnell.CubicInduction.discQ K < 0 ↔ discr K < 0 := by
    rw [← LanglandsTunnell.CubicInduction.discr_neg_iff K (integralBasis K), ← coe_discr, Int.cast_lt_zero]
  have hsign : (discr K).sign = (-1) ^ NumberField.InfinitePlace.nrComplexPlaces K := NumberField.sign_discr K
  unfold LanglandsTunnell.CubicInduction.lamSqArch
  by_cases hneg : discr K < 0
  · rw [if_pos (hiff.mpr hneg)]
    rw [Int.sign_eq_neg_one_of_neg hneg] at hsign
    rcases Nat.even_or_odd (NumberField.InfinitePlace.nrComplexPlaces K) with h | h
    · rw [h.neg_one_pow] at hsign
      norm_num at hsign
    · rw [h.neg_one_pow]
  · rw [if_neg (mt hiff.mp hneg)]
    have hpos : 0 < discr K := lt_of_le_of_ne (not_lt.mp hneg) (discr_ne_zero K).symm
    rw [Int.sign_eq_one_of_pos hpos] at hsign
    rcases Nat.even_or_odd (NumberField.InfinitePlace.nrComplexPlaces K) with h | h
    · rw [h.neg_one_pow]
    · rw [h.neg_one_pow] at hsign
      norm_num at hsign
