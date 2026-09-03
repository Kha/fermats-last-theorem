import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_mem_heckeAlgebra_qCoeff_one_eq_qCoeff_of_one_le
set_option autoImplicit false

theorem CuspForm.exists_mem_heckeAlgebra_qCoeff_one_eq_qCoeff_of_one_le (N : ℕ) [NeZero N] (k : ℤ) (hk : 1 ≤ k)
    (n : ℕ) (hn : 0 < n) :
    ∃ t ∈ CuspForm.heckeAlgebra N k (∅ : Set ℕ),
      ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) k,
        ModularFormClass.qCoeff (t f) 1 = ModularFormClass.qCoeff f n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_mem_heckeAlgebra_qCoeff_one_eq_qCoeff_of_one_le.solution
