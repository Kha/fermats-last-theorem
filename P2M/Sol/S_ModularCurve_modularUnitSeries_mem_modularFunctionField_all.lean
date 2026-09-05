import Definitions.Def_ModularCurve_ModularUnit
import P2M.Sol.S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import P2M.Util
namespace P2MW.S_ModularCurve_modularUnitSeries_mem_modularFunctionField_all
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

theorem solution (N : ℕ) [NeZero N] :
    ModularCurve.modularUnitSeries N ∈ ModularCurve.modularFunctionField N := by
  have h := ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC ℚ 0 N
    (fun h0 => NeZero.ne N (zero_dvd_iff.mp h0))
  rw [ModularCurve.modularFunctionFieldC_rat, ModularCurve.modularFunctionFieldFullC_rat] at h
  rw [h]
  exact ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull N
