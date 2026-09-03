import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
open ModularCurve
set_option autoImplicit false

theorem ModularCurve.ModularPolynomialData.evalSymm_of_one_lt
    (N : ℕ) [NeZero N] (hN : 1 < N) (data : ModularPolynomialData N) :
    EvalSymm data.Φ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt.solution
