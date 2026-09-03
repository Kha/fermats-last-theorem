import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.Lifts
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_eq_coeffMap_div_coeffMap_of_mem_modularFunctionFieldFull

theorem ModularCurve.exists_eq_coeffMap_div_coeffMap_of_mem_modularFunctionFieldFull (N : ℕ) [NeZero N]
    (x : LaurentSeries ℚ) (hx : x ∈ ModularCurve.modularFunctionFieldFull N) :
    ∃ a b : LaurentSeries ℤ, b ≠ 0 ∧
      x = ModularCurve.coeffMap (Int.castRingHom ℚ) a / ModularCurve.coeffMap (Int.castRingHom ℚ) b := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_eq_coeffMap_div_coeffMap_of_mem_modularFunctionFieldFull.solution
