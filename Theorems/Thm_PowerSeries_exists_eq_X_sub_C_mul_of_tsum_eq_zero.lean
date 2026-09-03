import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_eq_X_sub_C_mul_of_tsum_eq_zero

set_option autoImplicit false

theorem PowerSeries.exists_eq_X_sub_C_mul_of_tsum_eq_zero {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (a : L) (ha : ‖a‖ < ρ) (hFa : ∑' n, PowerSeries.coeff n F * a ^ n = 0) :
    ∃ H : PowerSeries L, F = (PowerSeries.X - PowerSeries.C a) * H ∧
      ∀ n, ‖PowerSeries.coeff n H‖ * ρ ^ (n + 1) ≤ M := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_eq_X_sub_C_mul_of_tsum_eq_zero.solution
