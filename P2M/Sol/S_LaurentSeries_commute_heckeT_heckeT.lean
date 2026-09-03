import Mathlib
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_LaurentSeries_commute_heckeU_heckeU
import Theorems.Thm_LaurentSeries_commute_heckeU_heckeV
import Theorems.Thm_LaurentSeries_commute_heckeV_heckeV
import P2M.Util
namespace P2MW.S_LaurentSeries_commute_heckeT_heckeT

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

open ModularCurve LaurentSeries

theorem solution (R : Type*) [CommRing R] (ℓ ℓ' : ℕ) (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (k : ℕ)
    (h : Nat.Coprime ℓ ℓ') :
    Commute (heckeT R ℓ hℓ k) (heckeT R ℓ' hℓ' k)  := by
  have h1 := commute_heckeU_heckeU R ℓ ℓ' hℓ hℓ'
  have h2 := commute_heckeU_heckeV R ℓ ℓ' hℓ hℓ' h
  have h3 := (commute_heckeU_heckeV R ℓ' ℓ hℓ' hℓ h.symm).symm
  have h4 := commute_heckeV_heckeV R ℓ ℓ' hℓ hℓ' h
  exact (h1.add_right (h2.smul_right _)).add_left ((h3.add_right (h4.smul_right _)).smul_left _)
