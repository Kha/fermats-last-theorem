import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_cuspForm_qExpansion_eq_coeffMap_mul_thetaL_pow_of_isIntegral
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_cuspForm_qExpansion_eq_coeffMap_mul_thetaL_pow_of_isIntegral (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m)
    (ι₀ : AlgebraicClosure ℚ →+* ℂ) (x : ↥(ModularCurve.modularFunctionFieldBar N))
    (h₁ : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({ModularCurve.jBar N} : Set ↥(ModularCurve.modularFunctionFieldBar N)))
      (x ^ 6 * ModularCurve.jBar N ^ (4 * m) *
        (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (3 * m)))
    (h₂ : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(ModularCurve.jBar N)⁻¹} : Set ↥(ModularCurve.modularFunctionFieldBar N)))
      (x ^ (2 * ModularCurve.dedekindPsi N) * ModularCurve.jBar N ^ (m * ModularCurve.dedekindPsi N + 1) *
        (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (m * ModularCurve.dedekindPsi N))) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ)),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 f) =
        ModularCurve.coeffMap ι₀ ((x : ↥(ModularCurve.modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) *
          ModularCurve.thetaL ℂ (ModularCurve.coeffEmb ℂ ModularCurve.jq) ^ m := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_cuspForm_qExpansion_eq_coeffMap_mul_thetaL_pow_of_isIntegral.solution
