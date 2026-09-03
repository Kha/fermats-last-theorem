import Mathlib
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_LaurentSeries_commute_heckeU_heckeT

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open ModularCurve LaurentSeries

theorem LaurentSeries.commute_heckeU_heckeT (R : Type*) [CommRing R] (p ℓ : ℕ) (hp : 0 < p) (hℓ : 0 < ℓ) (k : ℕ)
    (hpl : Nat.Coprime p ℓ) :
    Commute (heckeU R p hp) (heckeT R ℓ hℓ k) := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_commute_heckeU_heckeT.solution
