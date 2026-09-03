import Mathlib
import Definitions.Def_ModularCurve_LegendreJ
import P2M.Util
namespace P2MW.S_ModularCurve_legendreJ_one_sub

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "legendreJ"
p2m_open "ModularCurve"

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_legendreJ_one_sub.ModularCurve"

theorem solution {K : Type*} [Field K] (t : K) : legendreJ (1 - t) = legendreJ t := by
  simp only [legendreJ]
  ring
