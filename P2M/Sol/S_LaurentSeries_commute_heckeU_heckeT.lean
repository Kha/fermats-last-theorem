import Mathlib
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_LaurentSeries_commute_heckeU_heckeU
import Theorems.Thm_LaurentSeries_commute_heckeU_heckeV
import P2M.Util
namespace P2MW.S_LaurentSeries_commute_heckeU_heckeT

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

open ModularCurve LaurentSeries

theorem solution (R : Type*) [CommRing R] (p ℓ : ℕ) (hp : 0 < p) (hℓ : 0 < ℓ) (k : ℕ)
    (hpl : Nat.Coprime p ℓ) :
    Commute (heckeU R p hp) (heckeT R ℓ hℓ k)  :=
  (commute_heckeU_heckeU R p ℓ hp hℓ).add_right ((commute_heckeU_heckeV R p ℓ hp hℓ hpl).smul_right _)
