import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_adjoin_lambdaModC_of_pow_mul_mem
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.mem_adjoin_lambdaModC_of_pow_mul_mem (w : LaurentSeries ℚ)
    (hw : ∀ n : ℤ, n < 0 → w.coeff n = 0) (a : ℕ)
    (h : lambdaModC ℚ ^ a * w ∈ Algebra.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ))) :
    w ∈ Algebra.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_adjoin_lambdaModC_of_pow_mul_mem.solution
