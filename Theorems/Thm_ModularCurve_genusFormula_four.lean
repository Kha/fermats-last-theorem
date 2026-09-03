import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_genusFormula_four

set_option autoImplicit false

theorem ModularCurve.genusFormula_four : ModularCurve.genusFormula 4 = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_genusFormula_four.solution
