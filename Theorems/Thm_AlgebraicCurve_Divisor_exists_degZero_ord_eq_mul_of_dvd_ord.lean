import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_exists_degZero_ord_eq_mul_of_dvd_ord

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.exists_degZero_ord_eq_mul_of_dvd_ord {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (hn : n ≠ 0) [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0)
    (hdvd : ∀ v : Place K F, (n : ℤ) ∣ v.ord f) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      ∀ v : Place K F, v.ord f = (n : ℤ) * (D : Divisor K F) v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_exists_degZero_ord_eq_mul_of_dvd_ord.solution
