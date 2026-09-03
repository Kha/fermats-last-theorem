import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
namespace P2MW.S_ModularCurve_coeffEmb_jq_ne_zero

set_option autoImplicit false

theorem solution
    (L : Type) [Field L] [CharZero L] : ModularCurve.coeffEmb L ModularCurve.jq ≠ 0 :=
  (map_ne_zero (ModularCurve.coeffEmb L)).mpr ModularCurve.jq_ne_zero
