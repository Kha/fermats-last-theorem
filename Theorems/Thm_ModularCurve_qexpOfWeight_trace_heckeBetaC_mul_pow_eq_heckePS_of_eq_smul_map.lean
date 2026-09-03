import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open ModularCurve AlgebraicCurve

theorem ModularCurve.qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map
    (K : Type) [Field K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (m : ℕ) (hm : 1 ≤ m) (G : ↥(modularFunctionFieldC K N)) (φ : PowerSeries K)
    (hφ : HahnSeries.ofPowerSeries ℤ K φ = qexpOfWeight K (m : ℤ) ((G : ↥(modularFunctionFieldC K N)) : LaurentSeries K))
    (h : ↥(charLDegeneracyRoof K N ℓ))
    (hD : letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
      haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ)
      KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N))
        = h • KaehlerDifferential.map K K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
            (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N))) :
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
    HahnSeries.ofPowerSeries ℤ K (ModPForms.heckePS (2 * (m : ℤ)) ℓ φ)
      = qexpOfWeight K (m : ℤ)
          (HahnSeries.C ((ℓ : K) ^ (m - 1)) *
            (((Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ G * h ^ m) : ↥(modularFunctionFieldC K N)) : LaurentSeries K))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map.solution
