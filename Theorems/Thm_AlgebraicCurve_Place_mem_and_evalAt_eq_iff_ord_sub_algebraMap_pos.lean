import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) (hv : v.IsRational) (f : F) (a : K) (hfa : f ≠ algebraMap K F a) :
    (f ∈ v.toValuationSubring ∧ v.evalAt f = a) ↔ 0 < v.ord (f - algebraMap K F a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos.solution
