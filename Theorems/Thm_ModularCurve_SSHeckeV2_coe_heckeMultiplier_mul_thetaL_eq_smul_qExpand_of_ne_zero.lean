import Mathlib
import Definitions.Def_ModularCurve_SSHeckeV2
import P2M.Util
import P2M.Sol.S_ModularCurve_SSHeckeV2_coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.SSHeckeV2.coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓK : (ℓ : K) ≠ 0) :
    ((ModularCurve.heckeMultiplier N K ℓ : ↥(charLDegeneracyRoof K N ℓ)) : LaurentSeries K) * thetaL K (jqModC K)
      = (ℓ : K) • qExpand K ℓ (thetaL K (jqModC K)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SSHeckeV2_coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero.solution
