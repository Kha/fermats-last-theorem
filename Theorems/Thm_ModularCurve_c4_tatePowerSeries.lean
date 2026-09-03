import Definitions.Def_ModularCurve_TateFormal
import P2M.Util
import P2M.Sol.S_ModularCurve_c4_tatePowerSeries
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open PowerSeries HahnSeries ModularCurve
theorem ModularCurve.c4_tatePowerSeries : tatePowerSeries.c₄ = eisenstein4 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_c4_tatePowerSeries.solution
