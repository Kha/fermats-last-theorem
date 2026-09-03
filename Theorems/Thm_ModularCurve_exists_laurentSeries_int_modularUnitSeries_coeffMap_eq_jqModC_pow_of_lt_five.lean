import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five

set_option autoImplicit false

open ModularCurve

universe u

theorem ModularCurve.exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five
    (p : ℕ) [Fact p.Prime] (hp : p < 5) :
    ∃ x : LaurentSeries ℤ, coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p ∧
      ∀ (κ : Type u) [Field κ] [CharP κ p],
        coeffMap (Int.castRingHom κ) x = jqModC κ ^ (p - 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five.solution
