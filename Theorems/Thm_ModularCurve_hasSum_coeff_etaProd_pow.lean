import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_coeff_etaProd_pow
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.hasSum_coeff_etaProd_pow (a : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (etaProd ^ a) : ℤ) : ℂ) * q ^ m)
      ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ a) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_coeff_etaProd_pow.solution
