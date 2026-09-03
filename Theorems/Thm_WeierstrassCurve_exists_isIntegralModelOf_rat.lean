import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_isIntegralModelOf_rat

theorem WeierstrassCurve.exists_isIntegralModelOf_rat (E : WeierstrassCurve ℚ) :
    ∃ W : WeierstrassCurve ℤ, W.IsIntegralModelOf E := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_isIntegralModelOf_rat.solution
