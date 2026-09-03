import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_finite_of_finite_field

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.Affine.Point.finite_of_finite_field
    {F : Type*} [Field F] [DecidableEq F] [Finite F] (W : Affine F) :
    Finite W.Point := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_finite_of_finite_field.solution
