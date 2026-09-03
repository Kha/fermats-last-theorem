import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_frickeInvolutionBar_jF
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.frickeInvolutionBar_jF (p : ℕ) [Fact p.Prime] :
    frickeInvolutionBar (1 * p) (jF p) = jpF p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_frickeInvolutionBar_jF.solution
