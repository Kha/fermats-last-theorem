import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_jqModC_ne_zero

open ModularCurve
theorem ModularCurve.jqModC_ne_zero (K : Type*) [CommRing K] [Nontrivial K] :
    jqModC K ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqModC_ne_zero.solution
