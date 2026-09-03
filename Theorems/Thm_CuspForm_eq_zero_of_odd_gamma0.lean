import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_CuspForm_eq_zero_of_odd_gamma0

set_option autoImplicit false

theorem CuspForm.eq_zero_of_odd_gamma0 (N : ℕ) (k : ℤ) (hk : Odd k)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : f = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_eq_zero_of_odd_gamma0.solution
