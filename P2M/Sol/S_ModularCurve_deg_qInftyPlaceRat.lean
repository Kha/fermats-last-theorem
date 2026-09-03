import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_deg_of_toValuationSubring_eq_qIntegersBar
import P2M.Util
namespace P2MW.S_ModularCurve_deg_qInftyPlaceRat

open ModularCurve AlgebraicCurve

theorem solution {F : IntermediateField ℚ (LaurentSeries ℚ)} (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1) : (qInftyPlaceRat F h).deg = 1 :=
  ModularCurve.deg_of_toValuationSubring_eq_qIntegersBar h _ rfl
