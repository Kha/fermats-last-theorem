import Mathlib
import Definitions.Def_WeierstrassCurve_ConductorLevel
import Definitions.Def_WeierstrassCurve_ModularityLiftingConductor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isModularModelOfExactConductorLevel_of_level_conductorLevel

set_option autoImplicit false
theorem WeierstrassCurve.isModularModelOfExactConductorLevel_of_level_conductorLevel
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (h : W.IsModularModelOfLevel W.conductorLevel) :
    W.IsModularModelOfExactConductorLevel := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isModularModelOfExactConductorLevel_of_level_conductorLevel.solution
