import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_exists_mem_heckeAlgebra_qCoeff_apply_one_eq

theorem CuspForm.exists_mem_heckeAlgebra_qCoeff_apply_one_eq (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n ≠ 0) : ∃ t ∈ CuspForm.heckeAlgebra p 2 ∅, ∀ f : CuspForm (CongruenceSubgroup.Gamma0 p) 2, ModularFormClass.qCoeff (t f) 1 = ModularFormClass.qCoeff f n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_mem_heckeAlgebra_qCoeff_apply_one_eq.solution
