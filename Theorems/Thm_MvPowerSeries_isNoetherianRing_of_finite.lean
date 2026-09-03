import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_MvPowerSeries_isNoetherianRing_of_finite

universe u v w
theorem MvPowerSeries.isNoetherianRing_of_finite {σ : Type u} {R : Type v} [Finite σ] [CommRing R] [IsNoetherianRing R] : IsNoetherianRing (MvPowerSeries σ R) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.solution
