import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_aeval_lambdaModC_intCoeffs_descent
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.aeval_lambdaModC_intCoeffs_descent (P : Polynomial ℚ)
    (hP : IntCoeffs (Polynomial.aeval (lambdaModC ℚ) P)) (k : ℕ) : ∃ z : ℤ, P.coeff k = (z : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_aeval_lambdaModC_intCoeffs_descent.solution
