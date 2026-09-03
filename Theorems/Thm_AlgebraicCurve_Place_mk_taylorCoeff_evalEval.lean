import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_mk_taylorCoeff_evalEval

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem AlgebraicCurve.Place.mk_taylorCoeff_evalEval
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (G : Polynomial (Polynomial K)) :
    (PowerSeries.mk fun n =>
        taylorCoeff v t n ((G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y))
      = (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
          (PowerSeries.mk fun n => taylorCoeff v t n z) (PowerSeries.mk fun n => taylorCoeff v t n y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_mk_taylorCoeff_evalEval.solution
