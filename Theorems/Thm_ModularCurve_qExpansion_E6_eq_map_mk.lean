import Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpansion_E6_eq_map_mk

open UpperHalfPlane ModularForm Finset
theorem ModularCurve.qExpansion_E6_eq_map_mk :
    UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆ =
      PowerSeries.map (Int.castRingHom ℂ)
        (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansion_E6_eq_map_mk.solution
