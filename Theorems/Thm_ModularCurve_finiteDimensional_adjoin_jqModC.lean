import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteDimensional_adjoin_jqModC
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false

open IsLocalRing ModularCurve in

theorem ModularCurve.finiteDimensional_adjoin_jqModC
    {N : ℕ} [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) :
    FiniteDimensional
      ↥(IntermediateField.adjoin (ResidueField A)
        ({((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) : ↥(modularFunctionFieldC (ResidueField A) N))} : Set ↥(modularFunctionFieldC (ResidueField A) N)))
      ↥(modularFunctionFieldC (ResidueField A) N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteDimensional_adjoin_jqModC.solution
