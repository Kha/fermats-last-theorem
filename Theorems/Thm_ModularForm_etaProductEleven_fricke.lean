import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_etaProductEleven_fricke
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularForm.etaProductEleven_fricke {w : ℂ} (hw : w ∈ UpperHalfPlane.upperHalfPlaneSet) :
    ModularForm.eta (-1 / (11 * w)) ^ 2 * ModularForm.eta (11 * (-1 / (11 * w))) ^ 2 =
      -(11 * w ^ 2) * (ModularForm.eta w ^ 2 * ModularForm.eta (11 * w) ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_etaProductEleven_fricke.solution
