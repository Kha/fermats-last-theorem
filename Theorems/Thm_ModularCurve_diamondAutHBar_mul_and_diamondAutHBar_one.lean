import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import P2M.Util
import P2M.Sol.S_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve hiding exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply

theorem ModularCurve.diamondAutHBar_mul_and_diamondAutHBar_one (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (∀ a b : (ZMod M)ˣ, diamondAutHBar M H (a * b) = diamondAutHBar M H a * diamondAutHBar M H b) ∧
      diamondAutHBar M H 1 = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one.solution
