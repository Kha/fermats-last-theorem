import Mathlib
import Definitions.Def_ModularCurve_LegendreJ
import P2M.Util
import P2M.Sol.S_ModularCurve_legendreJ_inv

open ModularCurve
theorem ModularCurve.legendreJ_inv {K : Type*} [Field K] (t : K) : legendreJ t⁻¹ = legendreJ t := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_legendreJ_inv.solution
