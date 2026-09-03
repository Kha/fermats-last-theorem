import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
open ModularCurve
set_option autoImplicit false
theorem ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
    (k : Type*) [Field k]
    (ℓ : ℕ) [CharP k ℓ]
    (N : ℕ) [NeZero N] (q : ℕ) [NeZero q] [NeZero (N * q)]
    (hℓNq : ¬ ℓ ∣ N * q) :
    charLDegeneracyRoof k N q = modularFunctionFieldFullC k (N * q) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul.solution
