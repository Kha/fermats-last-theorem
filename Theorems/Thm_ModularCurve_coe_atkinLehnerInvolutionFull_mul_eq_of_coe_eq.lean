import Mathlib
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import P2M.Util
import P2M.Sol.S_ModularCurve_coe_atkinLehnerInvolutionFull_mul_eq_of_coe_eq
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.coe_atkinLehnerInvolutionFull_mul_eq_of_coe_eq
    (N₀ q ℓ : ℕ) [NeZero N₀] [NeZero ℓ] [Fact q.Prime] (hq : ¬ q ∣ N₀ * ℓ)
    (f : ↥(modularFunctionFieldFull (N₀ * q))) (f' : ↥(modularFunctionFieldFull (N₀ * ℓ * q)))
    (hf : ((f' : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) = ((f : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ)) :
    ((atkinLehnerInvolutionFull (N₀ * ℓ) q f' : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
      ((atkinLehnerInvolutionFull N₀ q f : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coe_atkinLehnerInvolutionFull_mul_eq_of_coe_eq.solution
