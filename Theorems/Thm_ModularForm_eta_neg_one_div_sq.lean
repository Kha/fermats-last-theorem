import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_eta_neg_one_div_sq
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularForm.eta_neg_one_div_sq {w : ℂ} (hw : w ∈ UpperHalfPlane.upperHalfPlaneSet) :
    ModularForm.eta (-1 / w) ^ 2 = -Complex.I * w * ModularForm.eta w ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_eta_neg_one_div_sq.solution
