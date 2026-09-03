import Definitions.Def_ModularCurve_QAdicPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_deg_qInftyPlaceBar

open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_qInftyPlaceBar (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) : (qInftyPlaceBar L F h).deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_deg_qInftyPlaceBar.solution
