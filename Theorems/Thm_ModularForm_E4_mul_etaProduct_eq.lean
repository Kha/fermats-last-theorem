import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_E4_mul_etaProduct_eq
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

theorem ModularForm.E4_mul_etaProduct_eq (z : UpperHalfPlane) :
    ModularForm.E₄ z * (ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (2 * (z : ℂ)) ^ 8 *
        ModularForm.eta (4 * (z : ℂ)) ^ 16) =
      ModularForm.eta (2 * (z : ℂ)) ^ 48 +
        224 * (ModularForm.eta (z : ℂ) ^ 8 * ModularForm.eta (2 * (z : ℂ)) ^ 24 *
          ModularForm.eta (4 * (z : ℂ)) ^ 16) +
        256 * (ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (4 * (z : ℂ)) ^ 32) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_E4_mul_etaProduct_eq.solution
