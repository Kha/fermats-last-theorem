import Definitions.Def_ModularCurve_ClassicalModularPolynomials
import Definitions.Def_ModularCurve_X0
import P2M.Sol.S_ModularCurve_nonempty_modularPolynomialData_of_squarefree
import Theorems.Thm_ModularCurve_ModularPolynomialData_phi_eq_phiTwo
import P2M.Util
namespace P2MW.S_ModularCurve_phiTwo_eval2_evalAtJ_jqN_two_eq_zero
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one

set_option autoImplicit false

open ModularCurve

theorem solution : phiTwo.eval₂ evalAtJ (jqN 2) = 0 := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData_of_squarefree 2 Nat.squarefree_two (by norm_num)
  rw [← ModularPolynomialData.phi_eq_phiTwo data]
  exact data.eval_eq_zero
