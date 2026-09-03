import Definitions.Def_ModularCurve_QAdicPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_deg_of_toValuationSubring_eq_qIntegersBar

open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_of_toValuationSubring_eq_qIntegersBar {F : IntermediateField ℚ (LaurentSeries ℚ)} [i : Algebra ℚ F] (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1) (v : Place ℚ F) (hv : v.toValuationSubring = qIntegersBar ℚ F) : v.deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_deg_of_toValuationSubring_eq_qIntegersBar.solution
