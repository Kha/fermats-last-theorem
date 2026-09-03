import Mathlib
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
namespace P2MW.S_LaurentSeries_heckeV_eq_qExpand

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

open ModularCurve LaurentSeries

theorem solution (R : Type*) [CommRing R] (ℓ : ℕ) [NeZero ℓ] (f : LaurentSeries R) :
    heckeV R ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ)) f = qExpand R ℓ f  := by
  ext n
  rw [coeff_heckeV]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
    rw [Int.mul_ediv_cancel_left _ hℓ0, qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd _ _ h]
