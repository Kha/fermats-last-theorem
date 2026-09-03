import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) {e : ℕ} (h : ∀ q, q < e → taylorCoeff v t q f = 0) :
    taylorRem v t f e = f * t⁻¹ ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [taylorRem_succ', h e (Nat.lt_succ_self e), map_zero, sub_zero,
      ih (fun q hq => h q (Nat.lt_succ_of_lt hq)), pow_succ, mul_assoc]
