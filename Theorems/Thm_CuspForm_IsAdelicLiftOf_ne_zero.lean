import Definitions.Def_CuspForm_AdelicLift
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOf_ne_zero

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.ne_zero
    {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφ : g.IsAdelicLiftOf φ)
    (hg : g ≠ 0) : φ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_ne_zero.solution
