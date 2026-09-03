import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_genusFormula_nine

set_option autoImplicit false

theorem ModularCurve.genusFormula_nine : ModularCurve.genusFormula 9 = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_genusFormula_nine.solution
