import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_isHaarMeasure_and_isMulRightInvariant_archMeasure

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.Converse.isHaarMeasure_and_isMulRightInvariant_archMeasure :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)
    RSCarrier.archMeasure.IsHaarMeasure ∧ RSCarrier.archMeasure.IsMulRightInvariant := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_isHaarMeasure_and_isMulRightInvariant_archMeasure.solution
