import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_kroneckerPairIntegral
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.jqNModC_one ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.kroneckerPairIntegral (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) :
    IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jqN ℓ - jq ^ ℓ) * qExpand ℚ N (jq - (jqN ℓ) ^ ℓ)))
      ∧ IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jq - (jqN ℓ) ^ ℓ) * qExpand ℚ N (jqN ℓ - jq ^ ℓ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_kroneckerPairIntegral.solution
