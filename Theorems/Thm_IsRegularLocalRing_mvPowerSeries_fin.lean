import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_mvPowerSeries_fin

theorem IsRegularLocalRing.mvPowerSeries_fin (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞]
    [IsDiscreteValuationRing 𝓞] (n : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin n) 𝓞) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_mvPowerSeries_fin.solution
