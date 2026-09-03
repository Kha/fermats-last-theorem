import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_etaProductEleven_add_one
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularForm.etaProductEleven_add_one (z : ℂ) :
    ModularForm.eta (z + 1) ^ 2 * ModularForm.eta (11 * (z + 1)) ^ 2 =
      ModularForm.eta z ^ 2 * ModularForm.eta (11 * z) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_etaProductEleven_add_one.solution
