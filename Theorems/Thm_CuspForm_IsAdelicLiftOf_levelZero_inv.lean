import Definitions.Def_CuspForm_AdelicLift
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOf_levelZero_inv

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.levelZero_inv {M : ℕ} (hM : M ≠ 0) {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφg : g.IsAdelicLiftOf φ) :
    ∀ u ∈ NumberField.AdelicLevel.finiteLevelZero (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel M),
      ∀ x, φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = φ x := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_levelZero_inv.solution
