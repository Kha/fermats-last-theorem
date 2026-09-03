import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_prime_X_sq_sub_C_X_mul_X_add_C_C

theorem PowerSeries.prime_X_sq_sub_C_X_mul_X_add_C_C
    {D : Type*} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D]
    {c : D} (hc0 : c ≠ 0) (hcu : ¬IsUnit c) :
    Prime (Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X +
      Polynomial.C (PowerSeries.C c) : Polynomial (PowerSeries D)) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_prime_X_sq_sub_C_X_mul_X_add_C_C.solution
