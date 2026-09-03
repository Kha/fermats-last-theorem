import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (hx : x ∉ Set.range (TwoChartIntegralModel.ιFin R F j).base) :
    ∃ 𝔮 : PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf R F j),
      TwoChartIntegralModel.jInvChartInf R F j ∈ 𝔮.asIdeal ∧ (TwoChartIntegralModel.ιInf R F j).base 𝔮 = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin.solution
