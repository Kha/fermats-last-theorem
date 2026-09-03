import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ell_add_of_forall_eq_ord

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.ell_add_of_forall_eq_ord
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] (D : Divisor K F) {P : Divisor K F}
    {f : F} (hf : f ≠ 0) (hP : ∀ v : Place K F, P v = v.ord f) :
    ell (D + P) = ell D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ell_add_of_forall_eq_ord.solution
