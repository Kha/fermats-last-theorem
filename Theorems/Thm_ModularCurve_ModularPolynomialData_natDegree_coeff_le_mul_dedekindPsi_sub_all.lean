import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub_all
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one

set_option autoImplicit false

open ModularCurve Polynomial
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub_all (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (i : ℕ) :
    (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub_all.solution
