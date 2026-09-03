import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_taylorShift_mul

set_option autoImplicit false

theorem PowerSeries.taylorShift_mul {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (a : L) (ha : ‖a‖ < ρ) :
    (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (F * G) * ((n + k).choose n : L) * a ^ k)
      = (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)
        * (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) G * ((n + k).choose n : L) * a ^ k) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_taylorShift_mul.solution
