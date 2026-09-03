import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_flat_subschemeIota_mul_comp_of_isInvertible

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.flat_subschemeIota_mul_comp_of_isInvertible
    {X T : Scheme.{u}} (q : X ⟶ T) (I J : X.IdealSheafData) (hI : I.IsInvertible)
    [Flat (I.subschemeι ≫ q)] [Flat (J.subschemeι ≫ q)] :
    Flat ((I * J).subschemeι ≫ q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_flat_subschemeIota_mul_comp_of_isInvertible.solution
