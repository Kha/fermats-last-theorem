import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq_qExpand
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve hiding relfinrank_qExpand_full relfinrank_full_eq_mul

theorem ModularCurve.finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq_qExpand
    (M ℓ : ℕ) [NeZero M] [Fact ℓ.Prime] (M' : ℕ) [NeZero M'] (hM' : M' = M * ℓ)
    (φ : ↥(modularFunctionFieldFull M) →+* ↥(modularFunctionFieldFull M'))
    (hφ : ∀ f : ↥(modularFunctionFieldFull M),
      ((φ f : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) = qExpand ℚ ℓ ((f : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) :
    @Module.finrank ↥(modularFunctionFieldFull M) ↥(modularFunctionFieldFull M') _ _ φ.toAlgebra.toModule =
      (if ℓ ∣ M then ℓ else ℓ + 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq_qExpand.solution
