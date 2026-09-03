import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_moduleFinite_adjoin_jChartFin_chartAlgFin

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.moduleFinite_adjoin_jChartFin_chartAlgFin
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (hj : Transcendental K₀ j)
    [FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F]
    [Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F] :
    Module.Finite ↥(Algebra.adjoin R ({jChartFin R F j} : Set ↥(chartAlgFin R F j))) ↥(chartAlgFin R F j) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_moduleFinite_adjoin_jChartFin_chartAlgFin.solution
