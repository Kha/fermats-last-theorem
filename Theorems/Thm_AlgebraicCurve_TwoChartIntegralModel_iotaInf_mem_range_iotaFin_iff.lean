import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_iotaInf_mem_range_iotaFin_iff

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
universe u

theorem AlgebraicCurve.TwoChartIntegralModel.iotaInf_mem_range_iotaFin_iff
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (𝔮 : PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf R F j)) :
    (TwoChartIntegralModel.ιInf R F j).base 𝔮 ∈ Set.range (TwoChartIntegralModel.ιFin R F j).base ↔
      TwoChartIntegralModel.jInvChartInf R F j ∉ 𝔮.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_iotaInf_mem_range_iotaFin_iff.solution
