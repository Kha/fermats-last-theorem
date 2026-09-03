import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_crossRatio_swap

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K : Type*} [Field K] (z z₀ x y : K) :
    crossRatio z z₀ x y = crossRatio x y z z₀ := by
  simp only [crossRatio]
  rw [show (x - z) * (y - z₀) = (z - x) * (z₀ - y) by ring, show (x - z₀) * (y - z) = (z - y) * (z₀ - x) by ring]
