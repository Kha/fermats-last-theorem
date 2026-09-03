import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_iotaInf_mem_range_iotaFin_iff

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (𝔮 : PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf R F j)) :
    (TwoChartIntegralModel.ιInf R F j).base 𝔮 ∈ Set.range (TwoChartIntegralModel.ιFin R F j).base ↔
      TwoChartIntegralModel.jInvChartInf R F j ∉ 𝔮.asIdeal := by
  have key : 𝔮 ∈ Set.range (TwoChartIntegralModel.fInf R F j).base ↔
      TwoChartIntegralModel.jInvChartInf R F j ∉ 𝔮.asIdeal := by
    rw [TwoChartIntegralModel.TwoChartsAux.range_fInf]
    exact Iff.rfl
  rw [← key]
  constructor
  · rintro ⟨x₀, hx⟩
    obtain ⟨u, -, hu⟩ := (TwoChartIntegralModel.TwoChartsAux.ιFin_eq_ιInf_iff R F j x₀ 𝔮).mp hx
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨(TwoChartIntegralModel.fFin R F j).base u,
      (TwoChartIntegralModel.TwoChartsAux.ιFin_eq_ιInf_iff R F j _ 𝔮).mpr ⟨u, rfl, hu⟩⟩
