import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_modularFunctionFieldFullC_one

open ModularCurve
theorem ModularCurve.modularFunctionFieldFullC_one (K : Type*) [Field K] :
    modularFunctionFieldFullC K 1 = modularFunctionFieldC K 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularFunctionFieldFullC_one.solution
