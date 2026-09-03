import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_isNoetherianRing_fin

theorem MvPowerSeries.isNoetherianRing_fin (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.solution
