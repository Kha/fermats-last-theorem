import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (e : ℕ) :
    (∀ q, q < e → taylorCoeff v t q f = 0) ↔ (e : ℤ) ≤ v.ord f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord.solution
