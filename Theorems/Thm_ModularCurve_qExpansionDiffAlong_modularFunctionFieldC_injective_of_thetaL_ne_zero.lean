import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpansionDiffAlong_modularFunctionFieldC_injective_of_thetaL_ne_zero
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.qExpansionDiffAlong_modularFunctionFieldC_injective_of_thetaL_ne_zero
    (K : Type*) [Field K] (N : ℕ) [Fact N.Prime] {L : Type*} [Field L] [Algebra K L]
    (σ : modularFunctionFieldC K N →ₐ[K] LaurentSeries L)
    (hsep : thetaL L (σ ⟨jqModC K, jqModC_mem K N⟩) ≠ 0) :
    Function.Injective (qExpansionDiffAlong σ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansionDiffAlong_modularFunctionFieldC_injective_of_thetaL_ne_zero.solution
