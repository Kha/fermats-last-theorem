import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.taylorCoeff_succ_eq_taylorCoeff_taylorRem_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) (r : ℕ) :
    taylorCoeff v t (r + 1) f = taylorCoeff v t r (taylorRem v t f 1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one.solution
