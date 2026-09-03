import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_coeffEmb_jq_mem_laurentBaseChange_x1FunctionField
attribute [-simp] ModularCurve.jqNModC_one

set_option autoImplicit false

theorem ModularCurve.coeffEmb_jq_mem_laurentBaseChange_x1FunctionField
    (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] :
    ModularCurve.coeffEmb L ModularCurve.jq ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffEmb_jq_mem_laurentBaseChange_x1FunctionField.solution
