import Mathlib
import P2M.Util
namespace P2MW.S_PowerSeries_coeff_zero_taylorShift

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace PowerSeries
p2m_export "PowerSeries" "coeff_mk mk C coeff"
p2m_open "PowerSeries"

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

end PowerSeries

open _root_.PowerSeries _root_.P2MW.S_PowerSeries_coeff_zero_taylorShift.PowerSeries in

theorem solution {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (F : PowerSeries L) (a : L) :
    PowerSeries.coeff 0 (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)
      = ∑' k, PowerSeries.coeff k F * a ^ k := by
  rw [PowerSeries.coeff_mk]
  refine tsum_congr fun k => ?_
  simp

#print axioms solution
