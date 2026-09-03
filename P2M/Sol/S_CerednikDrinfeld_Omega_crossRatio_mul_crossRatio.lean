import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_crossRatio_mul_crossRatio

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K : Type*} [Field K] (z w z₀ x y : K) (hwx : w ≠ x) (hwy : w ≠ y) :
    crossRatio z w x y * crossRatio w z₀ x y = crossRatio z z₀ x y := by
  have h : (w - y) * (w - x) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hwy) (sub_ne_zero.mpr hwx)
  rw [crossRatio, crossRatio, crossRatio, div_mul_div_comm]
  have e1 : (z - x) * (w - y) * ((w - x) * (z₀ - y)) = ((w - y) * (w - x)) * ((z - x) * (z₀ - y)) := by ring
  have e2 : (z - y) * (w - x) * ((w - y) * (z₀ - x)) = ((w - y) * (w - x)) * ((z - y) * (z₀ - x)) := by ring
  rw [e1, e2, mul_div_mul_left _ _ h]
