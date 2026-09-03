import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_norm_coeff_mul_mul_pow_le

set_option autoImplicit false

theorem PowerSeries.norm_coeff_mul_mul_pow_le {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 ≤ ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (n : ℕ) : ‖PowerSeries.coeff n (F * G)‖ * ρ ^ n ≤ M * M' := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_norm_coeff_mul_mul_pow_le.solution
