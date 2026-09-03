import Definitions.Def_ModularCurve_TateFormal
import P2M.Util
import P2M.Sol.S_ModularCurve_c6_tatePowerSeries
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open PowerSeries HahnSeries ModularCurve
theorem ModularCurve.c6_tatePowerSeries : tatePowerSeries.c₆ = -eisenstein6 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_c6_tatePowerSeries.solution
