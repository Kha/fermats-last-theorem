import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_crossRatio_swap

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.crossRatio_swap
    {K : Type*} [Field K] (z z₀ x y : K) :
    crossRatio z z₀ x y = crossRatio x y z z₀ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_crossRatio_swap.solution
