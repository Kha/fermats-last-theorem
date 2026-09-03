import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open ModularCurve hiding nonempty_modularPolynomialData transcendental_jqModC

theorem ModularCurve.exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ∃ (_ : Algebra (RatFunc K) ↥(modularFunctionFieldC K N)),
      IsScalarTower K (RatFunc K) ↥(modularFunctionFieldC K N) ∧
      algebraMap (RatFunc K) ↥(modularFunctionFieldC K N) RatFunc.X = ⟨jqModC K, jqModC_mem K N⟩ ∧
      Module.Finite (RatFunc K) ↥(modularFunctionFieldC K N) ∧
      Algebra.IsSeparable (RatFunc K) ↥(modularFunctionFieldC K N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable.solution
