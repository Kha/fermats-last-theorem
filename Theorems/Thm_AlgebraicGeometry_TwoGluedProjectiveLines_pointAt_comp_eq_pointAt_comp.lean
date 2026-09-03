import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_TwoGluedProjectiveLines_pointAt_comp_eq_pointAt_comp

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  NeronModelInfra AlgebraicGeometry.TwoGluedProjectiveLines

theorem AlgebraicGeometry.TwoGluedProjectiveLines.pointAt_comp_eq_pointAt_comp
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of κ))
    (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X) [IsClosedImmersion i₁]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase) (c d : κ)
    (h : i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ c)).1 =
      i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ d)).1) :
    (pointAt M₁ c).1 ≫ i₁ = (pointAt M₂ d).1 ≫ i₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_pointAt_comp_eq_pointAt_comp.solution
