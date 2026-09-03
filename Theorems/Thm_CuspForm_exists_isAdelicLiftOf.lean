import Definitions.Def_CuspForm_AdelicLift
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isAdelicLiftOf

theorem CuspForm.exists_isAdelicLiftOf {M : ℕ} (hM : M ≠ 0) (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    ∃ φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ, g.IsAdelicLiftOf φ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isAdelicLiftOf.solution
