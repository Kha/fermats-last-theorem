import Mathlib
import P2M.Util
import P2M.Sol.S_CuspForm_exists_ne_zero_gamma0_eleven
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem CuspForm.exists_ne_zero_gamma0_eleven :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 11) 2, f ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_ne_zero_gamma0_eleven.solution
