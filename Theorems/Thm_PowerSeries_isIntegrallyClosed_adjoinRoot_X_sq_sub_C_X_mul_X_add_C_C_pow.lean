import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow

theorem PowerSeries.isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow
    {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    (ϖ : D) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    IsIntegrallyClosed (AdjoinRoot (Polynomial.X ^ 2 -
      Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X +
      Polynomial.C (PowerSeries.C (ϖ ^ e)) : Polynomial (PowerSeries D))) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.solution
