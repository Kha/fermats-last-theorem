import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

import Theorems.Thm_AlgebraicCurve_Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) {e : ℕ} (h : ∀ q, q < e → taylorCoeff v t q f = 0) :
    taylorCoeff v t e f = v.evalAt (f * t⁻¹ ^ e) := by
  rw [taylorCoeff_eq, taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero v t f h]
