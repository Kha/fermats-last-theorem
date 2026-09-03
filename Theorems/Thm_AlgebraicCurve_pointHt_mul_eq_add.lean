import Definitions.Def_ModularCurve_JZeroHeightForm
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_pointHt_mul_eq_add

set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.pointHt_mul_eq_add {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (s : Fin a → F) (s' : Fin b → F)
    (hs : ∀ i, s i ≠ 0) (hs' : ∀ j, s' j ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) :
    pointHt (fun k : Fin (a * b) => s (finProdFinEquiv.symm k).1 * s' (finProdFinEquiv.symm k).2) v
      = pointHt s v + pointHt s' v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_pointHt_mul_eq_add.solution
