import Mathlib
import Definitions.Def_Patching_SystemTypes
import P2M.Util
import P2M.Sol.S_MvPowerSeries_depth_self_eq_ringKrullDim_fin_of_isDiscreteValuationRing

open IsLocalRing RingTheory
theorem MvPowerSeries.depth_self_eq_ringKrullDim_fin_of_isDiscreteValuationRing
    (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞] (n : ℕ) :
    (Module.depth (MvPowerSeries (Fin n) 𝓞) (MvPowerSeries (Fin n) 𝓞) : WithBot ℕ∞)
      = ringKrullDim (MvPowerSeries (Fin n) 𝓞) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_depth_self_eq_ringKrullDim_fin_of_isDiscreteValuationRing.solution
