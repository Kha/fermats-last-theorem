import Definitions.Def_CuspForm_ModPForms
import Mathlib.NumberTheory.ModularForms.Derivative
import P2M.Util
import P2M.Sol.S_ModularForm_exists_gamma0_coe_eq_serreDerivative
set_option autoImplicit false

theorem ModularForm.exists_gamma0_coe_eq_serreDerivative (N' : ℕ) [NeZero N'] (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma0 N') k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N') (k + 2),
      ⇑g = Derivative.serreDerivative (k : ℂ) ⇑f := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_gamma0_coe_eq_serreDerivative.solution
