import Mathlib
import Definitions.Def_ModularCurve_SSHeckeV2
import P2M.Util
import P2M.Sol.S_ModularCurve_SSHeckeV2_eq_heckeMultiplier_of_D_heckeBetaC_eq_smul_map
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.SSHeckeV2.eq_heckeMultiplier_of_D_heckeBetaC_eq_smul_map
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (h : ↥(charLDegeneracyRoof K N ℓ))
    (hD : letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ);
          haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ);
          KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N))
            = h • KaehlerDifferential.map K K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
                (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N))) :
    h = ModularCurve.heckeMultiplier N K ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SSHeckeV2_eq_heckeMultiplier_of_D_heckeBetaC_eq_smul_map.solution
