import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelP_isDomain_and_isIntegrallyClosed_univBase

theorem ModularCurve.LevelP.isDomain_and_isIntegrallyClosed_univBase (p : ℕ) (hp : p ≠ 0) :
    IsDomain (ModularCurve.LevelP.UnivBase p) ∧
      IsIntegrallyClosed (ModularCurve.LevelP.UnivBase p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelP_isDomain_and_isIntegrallyClosed_univBase.solution
