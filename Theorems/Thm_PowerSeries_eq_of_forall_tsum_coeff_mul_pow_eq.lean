import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_eq_of_forall_tsum_coeff_mul_pow_eq

set_option autoImplicit false

theorem PowerSeries.eq_of_forall_tsum_coeff_mul_pow_eq {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (h : ∀ z : L, ‖z‖ < ρ → ∑' n, PowerSeries.coeff n F * z ^ n = ∑' n, PowerSeries.coeff n G * z ^ n) :
    F = G := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_eq_of_forall_tsum_coeff_mul_pow_eq.solution
