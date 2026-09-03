import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_MvPowerSeries_isAdicComplete_maximalIdeal

universe u v w
theorem MvPowerSeries.isAdicComplete_maximalIdeal {σ : Type u} {R : Type v} [Finite σ] [CommRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries σ R)) (MvPowerSeries σ R) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_isAdicComplete_maximalIdeal.solution
