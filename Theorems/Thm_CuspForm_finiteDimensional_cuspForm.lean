import Mathlib.NumberTheory.ModularForms.Basic
import P2M.Util
import P2M.Sol.S_CuspForm_finiteDimensional_cuspForm
set_option autoImplicit false

theorem CuspForm.finiteDimensional_cuspForm (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_finiteDimensional_cuspForm.solution
