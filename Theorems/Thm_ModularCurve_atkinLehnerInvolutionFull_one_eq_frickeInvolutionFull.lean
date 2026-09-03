import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem ModularCurve.atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull
    (q : ℕ) [Fact q.Prime] :
    atkinLehnerInvolutionFull 1 q = frickeInvolutionFull (1 * q) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull.solution
