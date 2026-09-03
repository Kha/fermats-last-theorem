import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_jqN_mem_chartAlgFin_and_jFull_mem_chartAlg_jqN
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.jqN_mem_chartAlgFin_and_jFull_mem_chartAlg_jqN
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    (⟨jqN N, modularFunctionField_le_full N (jqN_mem N)⟩ : ↥(modularFunctionFieldFull N))
        ∈ chartAlgFin N ℓ ∧
      jFull N ∈ chartAlg N ℓ
        ({⟨jqN N, modularFunctionField_le_full N (jqN_mem N)⟩} : Set ↥(modularFunctionFieldFull N)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_jqN_mem_chartAlgFin_and_jFull_mem_chartAlg_jqN.solution
