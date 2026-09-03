import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even

set_option autoImplicit false

theorem CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even (N : ℕ) [NeZero N] (k : ℤ)
    (hk : Even k) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even.solution
