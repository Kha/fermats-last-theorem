import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem AlgebraicCurve.TwoChartIntegralModel.geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)] :
    GeometricallyIntegral (SmoothProperCurve.baseChange A (TwoChartIntegralModel.toBase A (↥K) j) L) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries.solution
