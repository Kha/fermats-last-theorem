import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_finite_setOf_not_mem_toValuationSubring_or_evalAt_mem

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.finite_setOf_not_mem_toValuationSubring_or_evalAt_mem
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hrat : ∀ v : Place K F, v.IsRational)
    (x : F) (hx : x ∉ Set.range (algebraMap K F)) (T : Finset K) :
    {v : Place K F | x ∉ v.toValuationSubring ∨ v.evalAt x ∈ (T : Set K)}.Finite := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_finite_setOf_not_mem_toValuationSubring_or_evalAt_mem.solution
