import Mathlib
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

theorem solution
    {k : Type} [Field k] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] : IsIntegral C :=
  GeometricallyIntegral.isIntegral_of_subsingleton c
