import Definitions.Def_CuspForm_AdelicLiftGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isAdelicLiftOfGamma1

set_option autoImplicit false

theorem CuspForm.exists_isAdelicLiftOfGamma1 {M : ℕ} (hM : M ≠ 0) (g : CuspForm (CongruenceSubgroup.Gamma1 M) 2) :
    ∃ φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ, CuspForm.IsAdelicLiftOfGamma1 g φ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isAdelicLiftOfGamma1.solution
