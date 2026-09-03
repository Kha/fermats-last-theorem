import Mathlib
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_ModularCurve_hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve KaehlerDifferential

theorem ModularCurve.hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] [NeZero ℓ]
    [IsCurveOver K ↥(modularFunctionFieldC K N)] [IsCurveOver K ↥(charLDegeneracyRoof K N ℓ)]
    (hN : (N : K) ≠ 0) (hpN : ¬ p ∣ N) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (m m' : ℕ) (hm : 1 ≤ m) (hm' : 1 ≤ m') (hmm' : m + m' = (p + 1) / 2)
    (hp_ : ↥(modularFunctionFieldC K N)) (hh : (hp_ : LaurentSeries K) = thetaL K (jqModC K) ^ (-(((p : ℤ) - 1) / 2)))
    (f : ↥(modularFunctionFieldC K N)) :
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
    (algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (p - 2 * m)) * hp_) •
        Differential.traceAlong (heckeBetaC K N ℓ)
          ((algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ (m - 1)) * ModularCurve.heckeMultiplier N K ℓ ^ m) •
            Differential.pullbackAlong (heckeAlphaC K N ℓ)
              (f • KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)))
      = (algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m' - 1)) *
          Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
            (heckeBetaC K N ℓ (f * hp_) * ModularCurve.heckeMultiplier N K ℓ ^ m')) •
        KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq.solution
