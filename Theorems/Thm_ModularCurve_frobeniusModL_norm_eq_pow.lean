import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_frobeniusModL_norm_eq_pow
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false
open ModularCurve AlgebraicCurve

theorem ModularCurve.frobeniusModL_norm_eq_pow
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (hfin : AlgebraicCurve.FiniteAlong K (frobeniusModL K N ℓ))
    (g : modularFunctionFieldFullC K N) :
    frobeniusModL K N ℓ
        (letI := AlgebraicCurve.algebraAlong (frobeniusModL K N ℓ)
         Algebra.norm (↥(modularFunctionFieldFullC K N)) g) = g ^ ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frobeniusModL_norm_eq_pow.solution
