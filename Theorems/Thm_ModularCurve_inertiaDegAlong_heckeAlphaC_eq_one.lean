import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_inertiaDegAlong_heckeAlphaC_eq_one
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
open ModularCurve AlgebraicCurve
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
theorem ModularCurve.inertiaDegAlong_heckeAlphaC_eq_one
    (k : Type*) [Field k] [IsAlgClosed k] (N q : ℕ) [NeZero N] [NeZero q]
    (hαc : HeckeAlphaCIntegral k N q)
    (W : AlgebraicCurve.Place k (charLDegeneracyRoof k N q)) :
    W.inertiaDegAlong (heckeAlphaC k N q) hαc = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_inertiaDegAlong_heckeAlphaC_eq_one.solution
