import Mathlib
import P2M.Util
import P2M.Sol.S_CuspForm_finiteDimensional_Gamma1

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.finiteDimensional_Gamma1 (M : ℕ) [NeZero M] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) k) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_finiteDimensional_Gamma1.solution
