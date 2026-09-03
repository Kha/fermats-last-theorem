import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ringHom_chartAlgInf_algebraMap_eq_coeff_zero_of_coe_eq_coeffEmb_jq
attribute [-simp] ModularCurve.jqNModC_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.exists_ringHom_chartAlgInf_algebraMap_eq_coeff_zero_of_coe_eq_coeffEmb_jq
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ∃ ψ : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →+* A,
      (∀ a : A, ψ (algebraMap A ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) a) = a) ∧
      (∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ∀ k : ℤ, k < 0 → (((f : ↥K) : LaurentSeries L)).coeff k = 0) ∧
      (∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
        algebraMap A L (ψ f) = (((f : ↥K) : LaurentSeries L)).coeff 0) ∧
      ψ (ModularCurve.TwoChart.jInvChartInf A (↥K) j) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ringHom_chartAlgInf_algebraMap_eq_coeff_zero_of_coe_eq_coeffEmb_jq.solution
