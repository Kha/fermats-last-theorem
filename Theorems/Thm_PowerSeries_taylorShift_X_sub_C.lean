import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_taylorShift_X_sub_C

set_option autoImplicit false

theorem PowerSeries.taylorShift_X_sub_C {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (w a : L) :
    (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) (PowerSeries.X - PowerSeries.C w) * ((n + k).choose n : L) * a ^ k)
      = PowerSeries.C (a - w) + PowerSeries.X := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_taylorShift_X_sub_C.solution
