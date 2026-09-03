import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_levelAutInputs_of_not_dvd

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

theorem ModularCurve.FullLevel.levelAutInputs_of_not_dvd (q : ℕ) [Fact q.Prime] (M' : ℕ)
    (hqM' : ¬ q ∣ M') : ModularCurve.FullLevel.LevelAutInputs q M' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_levelAutInputs_of_not_dvd.solution
