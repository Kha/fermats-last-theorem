import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    (I ^ n).IsInvertible := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact Scheme.IdealSheafData.isInvertible_top
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hI
