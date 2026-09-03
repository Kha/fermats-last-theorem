import Mathlib
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma0_eleven_apply_eq_eta_sq_mul_eta_sq
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem CuspForm.exists_gamma0_eleven_apply_eq_eta_sq_mul_eta_sq :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 11) 2,
      ∀ τ : UpperHalfPlane, f τ = ModularForm.eta (τ : ℂ) ^ 2 * ModularForm.eta (11 * (τ : ℂ)) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma0_eleven_apply_eq_eta_sq_mul_eta_sq.solution
