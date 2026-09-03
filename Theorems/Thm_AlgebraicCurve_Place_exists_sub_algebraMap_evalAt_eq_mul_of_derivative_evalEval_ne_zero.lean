import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_sub_algebraMap_evalAt_eq_mul_of_derivative_evalEval_ne_zero

set_option autoImplicit false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.Place.exists_sub_algebraMap_evalAt_eq_mul_of_derivative_evalEval_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (hsep : (Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y) ≠ 0) :
    ∃ h ∈ v.toValuationSubring,
      y - algebraMap K F (v.evalAt y) = h * (z - algebraMap K F (v.evalAt z)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_sub_algebraMap_evalAt_eq_mul_of_derivative_evalEval_ne_zero.solution
