import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Theorems.Thm_AlgebraicCurve_Place_taylorRem_succ_eq_taylorRem_taylorRem_one
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) (r : ℕ) :
    taylorCoeff v t (r + 1) f = taylorCoeff v t r (taylorRem v t f 1) := by
  rw [taylorCoeff_eq, taylorCoeff_eq, taylorRem_succ_eq_taylorRem_taylorRem_one]
