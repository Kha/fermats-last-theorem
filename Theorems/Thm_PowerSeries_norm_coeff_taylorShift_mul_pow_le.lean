import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_norm_coeff_taylorShift_mul_pow_le

set_option autoImplicit false

theorem PowerSeries.norm_coeff_taylorShift_mul_pow_le {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (a : L) (ha : ‖a‖ < ρ) (n : ℕ) :
    Summable (fun k : ℕ => PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k) ∧
      ‖PowerSeries.coeff n (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)‖ * ρ ^ n ≤ M := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_norm_coeff_taylorShift_mul_pow_le.solution
