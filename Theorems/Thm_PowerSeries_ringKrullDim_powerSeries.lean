import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_ringKrullDim_powerSeries

set_option autoImplicit false

universe u v

open IsLocalRing
theorem PowerSeries.ringKrullDim_powerSeries (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (PowerSeries R) = ringKrullDim R + 1 := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_ringKrullDim_powerSeries.solution
