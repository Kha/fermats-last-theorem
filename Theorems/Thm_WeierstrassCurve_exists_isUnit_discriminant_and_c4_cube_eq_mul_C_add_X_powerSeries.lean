import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_isUnit_discriminant_and_c4_cube_eq_mul_C_add_X_powerSeries

theorem WeierstrassCurve.exists_isUnit_discriminant_and_c4_cube_eq_mul_C_add_X_powerSeries
    (K : Type*) [Field K] (a : K) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728) :
    ∃ E : WeierstrassCurve (PowerSeries K), IsUnit E.Δ ∧ E.c₄ ^ 3 = E.Δ * (PowerSeries.C a + PowerSeries.X) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_isUnit_discriminant_and_c4_cube_eq_mul_C_add_X_powerSeries.solution
