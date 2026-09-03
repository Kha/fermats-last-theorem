import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_full_one_eq

open ModularCurve IntermediateField
theorem ModularCurve.full_one_eq : modularFunctionFieldFull 1 = modularFunctionField 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_full_one_eq.solution
