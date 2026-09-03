import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_qTwist_neg_one_lambdaModC_mul
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid
attribute [-simp] ModularCurve.ProjectiveLine.map_mk ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.qTwist_neg_one_lambdaModC_mul (K : Type*) [CommRing K] :
    qTwist (-1 : Kˣ) (lambdaModC K) * (16 * lambdaModC K - 1) = lambdaModC K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qTwist_neg_one_lambdaModC_mul.solution
