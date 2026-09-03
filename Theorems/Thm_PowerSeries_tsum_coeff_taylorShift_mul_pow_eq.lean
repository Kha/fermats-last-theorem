import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_tsum_coeff_taylorShift_mul_pow_eq

set_option autoImplicit false

theorem PowerSeries.tsum_coeff_taylorShift_mul_pow_eq {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (a : L) (ha : ‖a‖ < ρ) (b : L) (hb : ‖b‖ < ρ) :
    ∑' n, PowerSeries.coeff n (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k) * b ^ n
      = ∑' n, PowerSeries.coeff n F * (a + b) ^ n := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_tsum_coeff_taylorShift_mul_pow_eq.solution
