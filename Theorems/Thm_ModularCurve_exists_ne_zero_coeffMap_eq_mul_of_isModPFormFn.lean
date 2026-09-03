import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_ModPFormFn
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ne_zero_coeffMap_eq_mul_of_isModPFormFn

set_option autoImplicit false

theorem ModularCurve.exists_ne_zero_coeffMap_eq_mul_of_isModPFormFn
    (N : ℕ) [NeZero N] (m : ℕ) (X : LaurentSeries ℚ)
    (hXF : X ∈ ModularCurve.modularFunctionFieldFull N)
    (hX : ModularCurve.IsModPFormFn ℚ m X) :
    ∃ (c : ℤ) (Y : LaurentSeries ℤ), c ≠ 0 ∧
      ModularCurve.coeffMap (Int.castRingHom ℚ) Y = algebraMap ℚ (LaurentSeries ℚ) (c : ℚ) * X := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ne_zero_coeffMap_eq_mul_of_isModPFormFn.solution
