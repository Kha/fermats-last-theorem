import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_taylorRem_succ_eq_taylorRem_taylorRem_one

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.taylorRem_succ_eq_taylorRem_taylorRem_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) (r : ℕ) :
    taylorRem v t f (r + 1) = taylorRem v t (taylorRem v t f 1) r := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_taylorRem_succ_eq_taylorRem_taylorRem_one.solution
