import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_two_mul_tateUnivY_add_tateUnivX

set_option autoImplicit false

theorem ModularCurve.coeff_two_mul_tateUnivY_add_tateUnivX
    (i k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) (2 * ModularCurve.tateUnivY + ModularCurve.tateUnivX) =
      ((i : ℤ) - k) * MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) ModularCurve.tateUnivX := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_two_mul_tateUnivY_add_tateUnivX.solution
