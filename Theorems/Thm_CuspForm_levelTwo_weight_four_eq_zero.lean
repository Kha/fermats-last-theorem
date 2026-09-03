import Mathlib
import P2M.Util
import P2M.Sol.S_CuspForm_levelTwo_weight_four_eq_zero
set_option autoImplicit false

theorem CuspForm.levelTwo_weight_four_eq_zero
    (f : CuspForm (CongruenceSubgroup.Gamma0 2) 4) : f = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_levelTwo_weight_four_eq_zero.solution
