import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_divisor_eq_max_ord_sub_algebraMap

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_divisor_eq_max_ord_sub_algebraMap
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (x : F) (hx : Transcendental K x) (a : K) :
    ∃ D : Divisor K F, ∀ v : Place K F, D v = max 0 (v.ord (x - algebraMap K F a)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_divisor_eq_max_ord_sub_algebraMap.solution
