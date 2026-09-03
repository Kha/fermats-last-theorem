import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_norm_tsum_coeff_mul_pow_le_mul_prod

set_option autoImplicit false
open Classical in

theorem PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (S : Multiset L) (hS1 : ∀ w ∈ S, ‖w‖ < ρ)
    (hS : ∀ w ∈ S, (S.count w : ℕ∞)
      ≤ (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * w ^ k).order)
    (z : L) (hz : ‖z‖ < ρ) :
    ‖∑' n, PowerSeries.coeff n F * z ^ n‖ ≤ M * (S.map fun w => ‖z - w‖ / ρ).prod := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_norm_tsum_coeff_mul_pow_le_mul_prod.solution
