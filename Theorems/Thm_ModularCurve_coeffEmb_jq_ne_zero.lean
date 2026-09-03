import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_coeffEmb_jq_ne_zero

set_option autoImplicit false

theorem ModularCurve.coeffEmb_jq_ne_zero
    (L : Type) [Field L] [CharZero L] : ModularCurve.coeffEmb L ModularCurve.jq ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffEmb_jq_ne_zero.solution
