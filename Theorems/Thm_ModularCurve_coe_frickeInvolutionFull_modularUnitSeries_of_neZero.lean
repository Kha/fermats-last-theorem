import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries_of_neZero
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

theorem ModularCurve.coe_frickeInvolutionFull_modularUnitSeries_of_neZero (N : ℕ) [NeZero N] (hmem : ModularCurve.modularUnitSeries N ∈ ModularCurve.modularFunctionFieldFull N) : ((ModularCurve.frickeInvolutionFull N ⟨ModularCurve.modularUnitSeries N, hmem⟩ : ModularCurve.modularFunctionFieldFull N) : LaurentSeries ℚ) = (N : ℚ) ^ 12 • (ModularCurve.modularUnitSeries N)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries_of_neZero.solution
