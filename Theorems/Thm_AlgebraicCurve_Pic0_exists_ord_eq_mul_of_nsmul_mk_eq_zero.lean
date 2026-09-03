import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_exists_ord_eq_mul_of_nsmul_mk_eq_zero

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_ord_eq_mul_of_nsmul_mk_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : ↥(Divisor.degZero (K := K) (F := F))) (n : ℕ) (h : n • Pic0.mk D = 0) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = (n : ℤ) * (D : Divisor K F) v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_ord_eq_mul_of_nsmul_mk_eq_zero.solution
