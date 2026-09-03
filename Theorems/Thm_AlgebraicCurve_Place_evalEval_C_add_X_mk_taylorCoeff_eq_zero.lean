import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_evalEval_C_add_X_mk_taylorCoeff_eq_zero

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem AlgebraicCurve.Place.evalEval_C_add_X_mk_taylorCoeff_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0) :
    (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
        (PowerSeries.C (v.evalAt z) + PowerSeries.X)
        (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n y) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_evalEval_C_add_X_mk_taylorCoeff_eq_zero.solution
