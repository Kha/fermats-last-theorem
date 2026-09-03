import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one

open ModularCurve Polynomial
theorem ModularCurve.ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub
    (p : ℕ) [Fact p.Prime] (data : ModularPolynomialData p)
    (hsymm : EvalSymm data.Φ) (i : ℕ) :
    (data.Φ.coeff i).natDegree ≤ p * (dedekindPsi p - i) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub.solution
