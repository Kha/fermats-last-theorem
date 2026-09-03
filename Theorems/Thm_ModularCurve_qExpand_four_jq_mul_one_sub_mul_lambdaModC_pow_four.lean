import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four :
    qExpand ℚ 4 jq * (1 - 16 * lambdaModC ℚ) * lambdaModC ℚ ^ 4
      = (1 - 16 * lambdaModC ℚ + 16 * lambdaModC ℚ ^ 2) ^ 3 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four.solution
