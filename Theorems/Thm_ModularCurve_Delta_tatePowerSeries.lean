import Definitions.Def_ModularCurve_TateFormal
import P2M.Util
import P2M.Sol.S_ModularCurve_Delta_tatePowerSeries

open PowerSeries HahnSeries ModularCurve
theorem ModularCurve.Delta_tatePowerSeries :
    tatePowerSeries.Δ = PowerSeries.X * dedekindEtaUnit := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Delta_tatePowerSeries.solution
