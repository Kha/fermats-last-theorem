import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_dedekindPsi_eq_prod_primeFactors
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false

p2m_open "ModularCurve~dedekindPsi_mul_of_coprime~dedekindPsi_prime_pow"

theorem ModularCurve.dedekindPsi_eq_prod_primeFactors (N : ℕ) (hN : N ≠ 0) :
    dedekindPsi N = ∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1) * (p + 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_dedekindPsi_eq_prod_primeFactors.solution
