import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_eq_of_specializes_of_isMaximal_of_mem_chart

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.eq_of_specializes_of_isMaximal_of_mem_chart
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))

    (hx : (∃ y : ↥(XFin R F j), (ιFin R F j).base y = x ∧ y.asIdeal.IsMaximal ∧
        algebraMap R ↥(chartAlgFin R F j) ϖ ∈ y.asIdeal) ∨
      (∃ y : ↥(XInf R F j), (ιInf R F j).base y = x ∧ y.asIdeal.IsMaximal ∧
        algebraMap R ↥(chartAlgInf R F j) ϖ ∈ y.asIdeal))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (hz : x ⤳ z) :
    z = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_eq_of_specializes_of_isMaximal_of_mem_chart.solution
