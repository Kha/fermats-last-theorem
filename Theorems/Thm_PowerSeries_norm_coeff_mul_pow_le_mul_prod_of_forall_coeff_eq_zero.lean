import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero

set_option autoImplicit false
open Classical in

theorem PowerSeries.norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (e : ℕ) (he : ∀ n < e, PowerSeries.coeff n F = 0)
    (S : Multiset L) (hS1 : ∀ w ∈ S, ‖w‖ < ρ) (hS0 : ∀ w ∈ S, w ≠ 0)
    (hS : ∀ w ∈ S, (S.count w : ℕ∞)
      ≤ (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * w ^ k).order) :
    ‖PowerSeries.coeff e F‖ * ρ ^ e ≤ M * (S.map fun w => ‖w‖ / ρ).prod := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero.solution
