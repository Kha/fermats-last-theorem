import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_crossRatio_self

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K : Type*} [Field K] (z x y : K) (hzx : z ≠ x) (hzy : z ≠ y) :
    crossRatio z z x y = 1 := by
  have h : (z - y) * (z - x) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hzy) (sub_ne_zero.mpr hzx)
  rw [crossRatio, show (z - x) * (z - y) = (z - y) * (z - x) by ring, div_self h]
