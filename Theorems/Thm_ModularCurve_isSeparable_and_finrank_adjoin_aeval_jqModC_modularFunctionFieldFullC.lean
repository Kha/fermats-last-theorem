import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve

theorem ModularCurve.isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (r : Polynomial K) (hr : Polynomial.derivative r ≠ 0) :
    Algebra.IsSeparable
        (IntermediateField.adjoin K
          ({Polynomial.aeval (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) r} :
            Set (modularFunctionFieldFullC K N)))
        (modularFunctionFieldFullC K N) ∧
    Module.finrank
        (IntermediateField.adjoin K
          ({Polynomial.aeval (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) r} :
            Set (modularFunctionFieldFullC K N)))
        (modularFunctionFieldFullC K N) = r.natDegree * dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC.solution
