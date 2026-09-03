import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_coeff_zero_taylorShift

set_option autoImplicit false

theorem PowerSeries.coeff_zero_taylorShift {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (F : PowerSeries L) (a : L) :
    PowerSeries.coeff 0 (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)
      = ∑' k, PowerSeries.coeff k F * a ^ k := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_coeff_zero_taylorShift.solution
