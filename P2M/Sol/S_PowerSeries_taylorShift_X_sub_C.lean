import Mathlib
import P2M.Util
namespace P2MW.S_PowerSeries_taylorShift_X_sub_C

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace PowerSeries
p2m_export "PowerSeries" "coeff_mk mk coeff_C ext C coeff X coeff_X"
p2m_open "PowerSeries"

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

end PowerSeries

open _root_.PowerSeries _root_.P2MW.S_PowerSeries_taylorShift_X_sub_C.PowerSeries in

theorem solution {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (w a : L) :
    (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) (PowerSeries.X - PowerSeries.C w) * ((n + k).choose n : L) * a ^ k)
      = PowerSeries.C (a - w) + PowerSeries.X := by
  ext n
  rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C, PowerSeries.coeff_X]
  rcases n with _ | n
  ·
    rw [tsum_eq_sum (s := {0, 1}) (fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      have h2 : 2 ≤ 0 + k := by omega
      simp only [map_sub, PowerSeries.coeff_X, PowerSeries.coeff_C]
      rw [if_neg (by omega), if_neg (by omega)]
      simp)]
    rw [Finset.sum_pair (by norm_num)]
    simp [PowerSeries.coeff_X, PowerSeries.coeff_C]
    ring
  · rcases n with _ | n
    ·
      rw [tsum_eq_single 0 (fun k hk => by
        simp only [map_sub, PowerSeries.coeff_X, PowerSeries.coeff_C]
        rw [if_neg (by omega), if_neg (by omega)]
        simp)]
      simp [PowerSeries.coeff_X, PowerSeries.coeff_C]
    ·
      have hzero : (fun k : ℕ => PowerSeries.coeff (n + 1 + 1 + k) (PowerSeries.X - PowerSeries.C w)
          * ((n + 1 + 1 + k).choose (n + 1 + 1) : L) * a ^ k) = fun _ => 0 := by
        funext k
        simp only [map_sub, PowerSeries.coeff_X, PowerSeries.coeff_C]
        rw [if_neg (by omega), if_neg (by omega)]
        simp
      rw [hzero, tsum_zero, if_neg (by omega), if_neg (by omega), add_zero]

#print axioms solution
