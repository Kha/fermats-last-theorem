import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_etaProductEleven_smul_of_apply_one_zero_eq
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularForm.etaProductEleven_smul_of_apply_one_zero_eq (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ 1 0 = 11 * γ 0 1) (τ : UpperHalfPlane) :
    ModularForm.eta ((γ • τ : UpperHalfPlane) : ℂ) ^ 2 *
        ModularForm.eta (11 * ((γ • τ : UpperHalfPlane) : ℂ)) ^ 2 =
      UpperHalfPlane.denom (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (τ : ℂ) ^ (2 : ℤ) *
        (ModularForm.eta (τ : ℂ) ^ 2 * ModularForm.eta (11 * (τ : ℂ)) ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_etaProductEleven_smul_of_apply_one_zero_eq.solution
