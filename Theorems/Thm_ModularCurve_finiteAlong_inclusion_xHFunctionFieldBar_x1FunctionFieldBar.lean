import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteAlong_inclusion_xHFunctionFieldBar_x1FunctionFieldBar

set_option autoImplicit false

theorem ModularCurve.finiteAlong_inclusion_xHFunctionFieldBar_x1FunctionFieldBar
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hle : ModularCurve.xHFunctionFieldBar M H ≤ ModularCurve.x1FunctionFieldBar M) :
    AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (IntermediateField.inclusion hle) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteAlong_inclusion_xHFunctionFieldBar_x1FunctionFieldBar.solution
