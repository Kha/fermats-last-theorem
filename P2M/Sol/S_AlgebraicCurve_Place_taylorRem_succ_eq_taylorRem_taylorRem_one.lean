import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_taylorRem_succ_eq_taylorRem_taylorRem_one

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) (r : ℕ) :
    taylorRem v t f (r + 1) = taylorRem v t (taylorRem v t f 1) r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [taylorRem_succ, ih, ← taylorRem_succ]
