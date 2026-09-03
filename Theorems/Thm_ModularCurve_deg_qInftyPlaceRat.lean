import Definitions.Def_ModularCurve_QAdicPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_deg_qInftyPlaceRat

open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_qInftyPlaceRat {F : IntermediateField ℚ (LaurentSeries ℚ)} (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1) : (qInftyPlaceRat F h).deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_deg_qInftyPlaceRat.solution
