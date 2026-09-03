import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull

open ModularCurve

theorem ModularCurve.exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull
    (N : ℕ) [NeZero N] (x : ↥(modularFunctionFieldFull N)) (hx : IsAlgebraic ℚ x) :
    ∃ c : ℚ, x = algebraMap ℚ ↥(modularFunctionFieldFull N) c := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull.solution
