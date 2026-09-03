import Mathlib
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegral_adjoin_jq_atkinLehnerInvolutionFull
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve

theorem ModularCurve.isIntegral_adjoin_jq_atkinLehnerInvolutionFull
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (R : Type*) [CommRing R] [Algebra R ℚ] [Algebra R (modularFunctionFieldFull (N * p))]
    [IsScalarTower R ℚ (modularFunctionFieldFull (N * p))]
    (x : modularFunctionFieldFull (N * p))
    (hx : IsIntegral
      (Algebra.adjoin R ({⟨jq, modularFunctionField_le_full (N * p) (jq_mem (N * p))⟩} :
        Set (modularFunctionFieldFull (N * p)))) x) :
    IsIntegral
      (Algebra.adjoin R ({⟨jq, modularFunctionField_le_full (N * p) (jq_mem (N * p))⟩} :
        Set (modularFunctionFieldFull (N * p))))
      (atkinLehnerInvolutionFull N p x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegral_adjoin_jq_atkinLehnerInvolutionFull.solution
