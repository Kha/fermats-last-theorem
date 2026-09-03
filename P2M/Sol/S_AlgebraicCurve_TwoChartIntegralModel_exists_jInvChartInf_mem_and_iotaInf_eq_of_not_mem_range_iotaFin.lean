import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin.AlgebraicCurve"

universe u

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "TwoChartIntegralModel.chartAlgInf TwoChartIntegralModel.jInvChartInf TwoChartIntegralModel.fFin TwoChartIntegralModel.fInf TwoChartIntegralModel TwoChartIntegralModel.ιFin TwoChartIntegralModel.ιInf TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf TwoChartIntegralModel.TwoChartsAux.ιFin_eq_ιInf_iff TwoChartIntegralModel.TwoChartsAux.range_fInf" namespace TwoChartIntegralModel p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlgInf jInvChartInf fFin fInf ιFin ιInf mem_range_ιFin_or_mem_range_ιInf TwoChartsAux.ιFin_eq_ιInf_iff TwoChartsAux.range_fInf" namespace FinRangeAux end AlgebraicCurve.TwoChartIntegralModel.FinRangeAux
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel" in

theorem AlgebraicCurve.TwoChartIntegralModel.FinRangeAux.ιInf_mem_range_ιFin_iff
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

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (hx : x ∉ Set.range (TwoChartIntegralModel.ιFin R F j).base) :
    ∃ 𝔮 : PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf R F j),
      TwoChartIntegralModel.jInvChartInf R F j ∈ 𝔮.asIdeal ∧ (TwoChartIntegralModel.ιInf R F j).base 𝔮 = x := by
  obtain ⟨𝔮, rfl⟩ := (TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf R F j x).resolve_left hx
  exact ⟨𝔮, not_not.mp (fun h =>
    hx ((AlgebraicCurve.TwoChartIntegralModel.FinRangeAux.ιInf_mem_range_ιFin_iff R F j 𝔮).mpr h)), rfl⟩
