import Definitions.Def_ModularCurve_QAdicPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_algebraMap_coeff_zero_sub_not_isUnit_bar

open ModularCurve AlgebraicCurve

theorem ModularCurve.algebraMap_coeff_zero_sub_not_isUnit_bar (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) (f : (qInftyPlaceBar L F h).toValuationSubring) : ¬IsUnit (algebraMap L (qInftyPlaceBar L F h).toValuationSubring ((qSeriesBar L F (f : F)).coeff 0) - f) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_algebraMap_coeff_zero_sub_not_isUnit_bar.solution
