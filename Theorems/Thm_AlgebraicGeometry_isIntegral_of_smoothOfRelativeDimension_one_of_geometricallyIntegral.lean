import Mathlib
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral
    {k : Type} [Field k] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] : IsIntegral C := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral.solution
