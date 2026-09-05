import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull
import P2M.Util
namespace P2MW.S_ModularCurve_geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution (q : ℕ) [Fact q.Prime] :
    geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (1 * q))
        (atkinLehnerInvolutionFull 1 q)
      = frickeInvolutionBar (1 * q) := by
  rw [atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull, frickeInvolutionBar_def]

