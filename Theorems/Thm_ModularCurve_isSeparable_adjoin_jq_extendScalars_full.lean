import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QAdicPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_isSeparable_adjoin_jq_extendScalars_full
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.isSeparable_adjoin_jq_extendScalars_full (L : Type*) [Field L] [Algebra ℚ L] (N M : ℕ) [NeZero N] [NeZero M] (hle : laurentBaseChange L (modularFunctionFieldFull N) ≤ laurentBaseChange L (modularFunctionFieldFull M)) : Algebra.IsSeparable (IntermediateField.adjoin L ({algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩} : Set (IntermediateField.extendScalars hle))) (IntermediateField.extendScalars hle) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isSeparable_adjoin_jq_extendScalars_full.solution
