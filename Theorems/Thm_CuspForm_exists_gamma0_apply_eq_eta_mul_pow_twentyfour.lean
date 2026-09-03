import Mathlib
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma0_apply_eq_eta_mul_pow_twentyfour
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem CuspForm.exists_gamma0_apply_eq_eta_mul_pow_twentyfour (N : ℕ) [NeZero N] :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 12,
      ∀ τ : UpperHalfPlane, g τ = ModularForm.eta (N * (τ : ℂ)) ^ 24 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma0_apply_eq_eta_mul_pow_twentyfour.solution
