import Mathlib
import Theorems.Thm_PowerSeries_norm_coeff_taylorShift_mul_pow_le
import P2M.Util
namespace P2MW.S_PowerSeries_taylorShift_add

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace PowerSeries
p2m_export "PowerSeries" "coeff_mk mk ext coeff norm_coeff_taylorShift_mul_pow_le"
p2m_open "PowerSeries"

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

end PowerSeries

open _root_.PowerSeries _root_.P2MW.S_PowerSeries_taylorShift_add.PowerSeries in

theorem solution {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (a : L) (ha : ‖a‖ < ρ) :
    (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (F + G) * ((n + k).choose n : L) * a ^ k)
      = (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)
        + (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) G * ((n + k).choose n : L) * a ^ k) := by
  ext n
  simp only [map_add, PowerSeries.coeff_mk]
  rw [← ((norm_coeff_taylorShift_mul_pow_le F hρ hF a ha n).1).tsum_add
    ((norm_coeff_taylorShift_mul_pow_le G hρ hG a ha n).1)]
  refine tsum_congr fun k => ?_
  ring

#print axioms solution
