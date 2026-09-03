import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldC_mul
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldC_mul
    (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hpN : ¬ p ∣ N) (hpℓ : p ≠ ℓ) :
    ModularCurve.charLDegeneracyRoof κ N ℓ = ModularCurve.modularFunctionFieldC κ (N * ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldC_mul.solution
