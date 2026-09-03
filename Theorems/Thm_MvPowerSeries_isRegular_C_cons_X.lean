import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Regular.RegularSequence
import P2M.Util
import P2M.Sol.S_MvPowerSeries_isRegular_C_cons_X

universe u
theorem MvPowerSeries.isRegular_C_cons_X {R : Type u} [CommRing R] (n : ℕ) {ϖ : R}
    (hϖ : ϖ ∈ nonZeroDivisors R) (hu : ¬IsUnit ϖ) :
    RingTheory.Sequence.IsRegular (MvPowerSeries (Fin n) R)
      (MvPowerSeries.C ϖ :: List.ofFn (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_isRegular_C_cons_X.solution
