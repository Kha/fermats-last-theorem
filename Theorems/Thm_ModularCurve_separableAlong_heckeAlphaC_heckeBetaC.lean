import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve AlgebraicCurve

theorem ModularCurve.separableAlong_heckeAlphaC_heckeBetaC
    (k : Type*) [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
    (N q : ℕ) [NeZero N] [NeZero q] [Fact q.Prime] (hℓ : ¬ ℓ ∣ N * q) :
    SeparableAlong k (heckeAlphaC k N q) ∧ SeparableAlong k (heckeBetaC k N q) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC.solution
