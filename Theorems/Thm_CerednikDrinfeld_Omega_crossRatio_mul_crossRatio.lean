import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_crossRatio_mul_crossRatio

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.crossRatio_mul_crossRatio
    {K : Type*} [Field K] (z w z₀ x y : K) (hwx : w ≠ x) (hwy : w ≠ y) :
    crossRatio z w x y * crossRatio w z₀ x y = crossRatio z z₀ x y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_crossRatio_mul_crossRatio.solution
