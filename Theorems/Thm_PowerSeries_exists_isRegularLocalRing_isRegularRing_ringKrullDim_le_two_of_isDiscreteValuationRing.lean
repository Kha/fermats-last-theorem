import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_isRegularLocalRing_isRegularRing_ringKrullDim_le_two_of_isDiscreteValuationRing

set_option autoImplicit false

open IsLocalRing

theorem PowerSeries.exists_isRegularLocalRing_isRegularRing_ringKrullDim_le_two_of_isDiscreteValuationRing
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (p : ℕ) (hpO : ((p : ℕ) : O) ∈ maximalIdeal O) (hpO0 : ((p : ℕ) : O) ≠ 0) :
    ∃ (_ : IsRegularLocalRing (PowerSeries O)) (_ : IsRegularRing (PowerSeries O))
      (_ : IsAdicComplete (maximalIdeal (PowerSeries O)) (PowerSeries O))
      (_ : IsLocalHom (algebraMap O (PowerSeries O))),
      ringKrullDim (PowerSeries O) ≤ 2 ∧ ((p : ℕ) : PowerSeries O) ≠ 0 ∧
        ((p : ℕ) : PowerSeries O) ∈ maximalIdeal (PowerSeries O) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_isRegularLocalRing_isRegularRing_ringKrullDim_le_two_of_isDiscreteValuationRing.solution
