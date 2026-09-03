import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_summable_and_norm_tsum_coeff_mul_pow_le

set_option autoImplicit false

theorem PowerSeries.summable_and_norm_tsum_coeff_mul_pow_le {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (z : L) (hz : ‖z‖ < ρ) :
    Summable (fun n => PowerSeries.coeff n F * z ^ n) ∧ ‖∑' n, PowerSeries.coeff n F * z ^ n‖ ≤ M := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_summable_and_norm_tsum_coeff_mul_pow_le.solution
