import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_tsum_coeff_mul_mul_pow_eq_of_norm_lt

set_option autoImplicit false

theorem PowerSeries.tsum_coeff_mul_mul_pow_eq_of_norm_lt {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (z : L) (hz : ‖z‖ < ρ) :
    ∑' n, PowerSeries.coeff n (F * G) * z ^ n
      = (∑' n, PowerSeries.coeff n F * z ^ n) * ∑' n, PowerSeries.coeff n G * z ^ n := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_tsum_coeff_mul_mul_pow_eq_of_norm_lt.solution
