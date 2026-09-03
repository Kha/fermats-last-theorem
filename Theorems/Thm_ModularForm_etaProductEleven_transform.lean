import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_etaProductEleven_transform
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularForm.etaProductEleven_transform {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 11) (τ : UpperHalfPlane) :
    ModularForm.eta ((γ • τ : UpperHalfPlane) : ℂ) ^ 2 *
        ModularForm.eta (11 * ((γ • τ : UpperHalfPlane) : ℂ)) ^ 2 =
      UpperHalfPlane.denom (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (τ : ℂ) ^ (2 : ℤ) *
        (ModularForm.eta (τ : ℂ) ^ 2 * ModularForm.eta (11 * (τ : ℂ)) ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_etaProductEleven_transform.solution
