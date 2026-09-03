import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_divisor_forall_eq_weightFloor

set_option autoImplicit false

theorem AlgebraicCurve.exists_divisor_forall_eq_weightFloor
    (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
    (y : F) (m : ℕ) :
    ∃ D : AlgebraicCurve.Divisor K F, ∀ w : AlgebraicCurve.Place K F,
      D w = (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
          + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
          + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_divisor_forall_eq_weightFloor.solution
