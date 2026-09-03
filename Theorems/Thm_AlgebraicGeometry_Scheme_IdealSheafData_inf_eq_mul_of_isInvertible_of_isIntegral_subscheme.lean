import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_inf_eq_mul_of_isInvertible_of_isIntegral_subscheme

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.inf_eq_mul_of_isInvertible_of_isIntegral_subscheme
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible)
    [IsIntegral I.subscheme] [IsIntegral J.subscheme] (hIJ : ¬ I ≤ J) (hJI : ¬ J ≤ I) :
    I ⊓ J = I * J := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_inf_eq_mul_of_isInvertible_of_isIntegral_subscheme.solution
