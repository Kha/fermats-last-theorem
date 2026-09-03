import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_and_isInvertible_of_mul_of_sup_eq_top

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_and_isInvertible_of_mul_of_sup_eq_top
    {X : Scheme.{u}} {I J : X.IdealSheafData} (hIJ : (I * J).IsInvertible) (hcop : I ⊔ J = ⊤) :
    I.IsInvertible ∧ J.IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_and_isInvertible_of_mul_of_sup_eq_top.solution
