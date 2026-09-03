import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel

set_option autoImplicit false

universe u

open AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.mul_left_cancel {X : Scheme.{u}}
    {I J J' : X.IdealSheafData} (hI : I.IsInvertible) (h : I * J = I * J') : J = J' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel.solution
