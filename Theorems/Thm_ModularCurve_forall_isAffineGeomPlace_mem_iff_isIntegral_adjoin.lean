import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

noncomputable section

open AlgebraicCurve

theorem ModularCurve.forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin
    {N : ℕ} [NeZero N] {k : Type*} [Field k] (hN : (N : k) ≠ 0) (f : ↥(modularFunctionFieldC k N)) :
    (∀ u : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N u → f ∈ u.toValuationSubring) ↔
      IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) f := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin.solution

end
