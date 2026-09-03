import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange
attribute [-simp] ModularCurve.jqNModC_one

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange
    (Γ : Subgroup SL(2, ℤ))
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ∃ y : LaurentSeries A,
        ModularCurve.coeffMap (algebraMap A L) y = ((b : ↥K) : LaurentSeries L)) ∧
    (∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ∃ y : LaurentSeries A,
        ModularCurve.coeffMap (algebraMap A L) y = ((b : ↥K) : LaurentSeries L)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange.solution
