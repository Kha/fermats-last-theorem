import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import P2M.Util
import P2M.Sol.S_ModularCurve_isKummerGenerator_two_hasseRootFn_of_charP_three

set_option autoImplicit false

theorem ModularCurve.isKummerGenerator_two_hasseRootFn_of_charP_three
    (κ : Type) [Field κ] [CharP κ 3] (M : ℕ) [NeZero M] (w : ModularCurve.IntegralWeightOneForm κ M) :
    ModularCurve.IgusaCover.IsKummerGenerator 2 (ModularCurve.x1FunctionFieldC κ M) w.hasseRootFn := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isKummerGenerator_two_hasseRootFn_of_charP_three.solution
