import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient

set_option autoImplicit false

open IsLocalRing

theorem MvPowerSeries.isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient
    (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
    (n : ℕ) (J : Ideal (MvPowerSeries (Fin n) W)) :
    IsNoetherianRing (MvPowerSeries (Fin n) W ⧸ J) ∧
      IsAdicComplete ((maximalIdeal (MvPowerSeries (Fin n) W)).map (Ideal.Quotient.mk J))
        (MvPowerSeries (Fin n) W ⧸ J) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.solution
