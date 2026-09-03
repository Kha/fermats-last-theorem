import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_mk_taylorCoeff_eq_C_add_X

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem AlgebraicCurve.Place.mk_taylorCoeff_eq_C_add_X
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z : F} (hz : z ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1) :
    (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n z)
      = PowerSeries.C (v.evalAt z) + PowerSeries.X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_mk_taylorCoeff_eq_C_add_X.solution
