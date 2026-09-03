import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import P2M.Util
import P2M.Sol.S_ModularCurve_diffQExp_x1FunctionFieldBar_injective

theorem ModularCurve.diffQExp_x1FunctionFieldBar_injective (M : ℕ) [NeZero M] :
    Function.Injective ⇑(ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diffQExp_x1FunctionFieldBar_injective.solution
