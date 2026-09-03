import Mathlib
import Definitions.Def_Patching_SystemTypes
import P2M.Util
import P2M.Sol.S_MvPowerSeries_depth_self_fin_eq_of_isDiscreteValuationRing

open IsLocalRing RingTheory
theorem MvPowerSeries.depth_self_fin_eq_of_isDiscreteValuationRing
    (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞] (n : ℕ) :
    Module.depth (MvPowerSeries (Fin n) 𝓞) (MvPowerSeries (Fin n) 𝓞) = ((n + 1 : ℕ) : ℕ∞) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_depth_self_fin_eq_of_isDiscreteValuationRing.solution
