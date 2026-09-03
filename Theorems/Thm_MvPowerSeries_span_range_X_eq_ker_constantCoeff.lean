import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.Order
import P2M.Util
import P2M.Sol.S_MvPowerSeries_span_range_X_eq_ker_constantCoeff

open MvPowerSeries
theorem MvPowerSeries.span_range_X_eq_ker_constantCoeff {R : Type*} [CommRing R] (n : ℕ) :
    Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) R)) =
      RingHom.ker (constantCoeff : MvPowerSeries (Fin n) R →+* R) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_span_range_X_eq_ker_constantCoeff.solution
