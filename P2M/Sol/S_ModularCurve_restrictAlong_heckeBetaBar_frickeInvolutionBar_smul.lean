module

public import Mathlib
public import Definitions.Def_ModularCurve_HeckeOperator
public import Definitions.Def_ModularCurve_CuspidalClass
public import Definitions.Def_ModularCurve_AtkinLehnerPartial
public import Theorems.Thm_AlgebraicCurve_Place_smul_restrictAlong
public import Theorems.Thm_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

theorem solution (q : ℕ) [NeZero q]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (frickeInvolutionBar (1 * q) • W).restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ
      = W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα := by
  rw [Place.smul_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
      (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hβ hα (frickeInvolutionBar (1 * q)) 1
      (fun x => ?_) W, one_smul]
  rw [AlgEquiv.one_apply]
  exact (DFunLike.congr_fun (frickeInvolutionBar_comp_heckeAlphaBar_one q) x).symm
