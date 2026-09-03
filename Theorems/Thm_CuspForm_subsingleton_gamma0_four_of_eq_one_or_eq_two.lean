import Mathlib.NumberTheory.ModularForms.Basic
import P2M.Util
import P2M.Sol.S_CuspForm_subsingleton_gamma0_four_of_eq_one_or_eq_two

set_option autoImplicit false

theorem CuspForm.subsingleton_gamma0_four_of_eq_one_or_eq_two (N' : ℕ) (hN' : N' = 1 ∨ N' = 2) :
    Subsingleton (CuspForm (CongruenceSubgroup.Gamma0 N') (4 : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_subsingleton_gamma0_four_of_eq_one_or_eq_two.solution
