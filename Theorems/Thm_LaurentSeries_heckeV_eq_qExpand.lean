import Mathlib
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_LaurentSeries_heckeV_eq_qExpand

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open ModularCurve LaurentSeries

theorem LaurentSeries.heckeV_eq_qExpand (R : Type*) [CommRing R] (ℓ : ℕ) [NeZero ℓ] (f : LaurentSeries R) :
    heckeV R ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ)) f = qExpand R ℓ f := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_heckeV_eq_qExpand.solution
