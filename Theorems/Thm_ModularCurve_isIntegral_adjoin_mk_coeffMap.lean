import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegral_adjoin_mk_coeffMap
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.isIntegral_adjoin_mk_coeffMap {O : Type*} [CommRing O] {K : Type*}
    [Field K] (res : O →+* K) (N : ℕ) [NeZero N] (Q : Polynomial (Polynomial O))
    (z : LaurentSeries O)
    (hzrep : z = ((Q.map (Polynomial.aeval (jqModC O)).toRingHom).eval (jqNModC O N)))
    (hmem : coeffMap res z ∈ modularFunctionFieldC K N) :
    IsIntegral
      (Algebra.adjoin K ({(⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N)} :
        Set (modularFunctionFieldC K N)))
      (⟨coeffMap res z, hmem⟩ : modularFunctionFieldC K N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegral_adjoin_mk_coeffMap.solution
