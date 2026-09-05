module

public import Mathlib
public import Definitions.Def_ModularCurve_HeckeOperator
public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul

@[expose] public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open AlgebraicCurve ModularCurve
theorem ModularCurve.restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul (q : ℕ) [NeZero q]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (frickeInvolutionBar (1 * q) • W).restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα
      = W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul.solution
