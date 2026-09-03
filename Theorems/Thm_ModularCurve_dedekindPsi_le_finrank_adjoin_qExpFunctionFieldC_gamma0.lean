import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
    (K : Type*) [Field K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (x : ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K)
    [FiniteDimensional
      (IntermediateField.adjoin K
        ({x} : Set (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))))
      (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))] :
    ModularCurve.dedekindPsi M ≤
      Module.finrank
        (IntermediateField.adjoin K
          ({x} : Set (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))))
        (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0.solution
