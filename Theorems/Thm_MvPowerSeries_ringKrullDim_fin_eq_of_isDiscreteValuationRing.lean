import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing
attribute [-instance] instTopologicallyFGOfFiniteType

theorem MvPowerSeries.ringKrullDim_fin_eq_of_isDiscreteValuationRing
    (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞] (n : ℕ) :
    ringKrullDim (MvPowerSeries (Fin n) 𝓞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing.solution
