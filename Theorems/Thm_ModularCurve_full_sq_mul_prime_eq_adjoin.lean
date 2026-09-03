import Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_full_sq_mul_prime_eq_adjoin
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.full_sq_mul_prime_eq_adjoin (p ℓ : ℕ) [hp : Fact (Nat.Prime p)] [hl : Fact (Nat.Prime ℓ)] (hpl : p ≠ ℓ) : modularFunctionFieldFull (p * p * ℓ) = IntermediateField.adjoin ℚ ({jq, jqN ℓ, jqN p, jqN (p * p)} : Set (LaurentSeries ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_full_sq_mul_prime_eq_adjoin.solution
