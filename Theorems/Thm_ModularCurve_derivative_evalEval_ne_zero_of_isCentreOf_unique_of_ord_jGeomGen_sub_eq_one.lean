import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_derivative_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jGeomGen_sub_eq_one
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve Polynomial

theorem ModularCurve.derivative_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jGeomGen_sub_eq_one
    (q : ℕ) (k : Type*) [Field k] [Fact q.Prime] [CharP k q] [IsAlgClosed k]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (data : ModularPolynomialData N)
    (v : Place k ↥(modularFunctionFieldC k N)) (c : k × k) (hc : IsCentreOf k N c v)
    (huniq : ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v)
    (hord : v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1) :
    (Polynomial.derivative (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval c.1 c.2 ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_derivative_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jGeomGen_sub_eq_one.solution
