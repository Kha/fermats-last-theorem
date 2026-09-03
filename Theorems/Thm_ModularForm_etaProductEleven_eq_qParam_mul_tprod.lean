import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_etaProductEleven_eq_qParam_mul_tprod
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularForm.etaProductEleven_eq_qParam_mul_tprod (z : ℂ) :
    ModularForm.eta z ^ 2 * ModularForm.eta (11 * z) ^ 2 =
      Function.Periodic.qParam 1 z *
        ((∏' n : ℕ, (1 - ModularForm.eta_q n z)) ^ 2 *
          (∏' n : ℕ, (1 - ModularForm.eta_q n (11 * z))) ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_etaProductEleven_eq_qParam_mul_tprod.solution
