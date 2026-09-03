import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import Definitions.Def_ModularCurve_ModularUnit
import P2M.Util
import P2M.Sol.S_ModularCurve_kirchhoffCount_eq_eisensteinNumerator_of_massFormula

open ModularCurve Finset
namespace ModularCurve
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem kirchhoffCount_eq_eisensteinNumerator_of_massFormula
    (e : ι → ℕ) (p : ℕ)
    (he : ∀ x, e x = 1 ∨ e x = 2 ∨ e x = 3)
    (h2 : ({x | e x = 2} : Set ι).Subsingleton)
    (h3 : ({x | e x = 3} : Set ι).Subsingleton)
    (hmass : ∑ x, ((e x : ℚ))⁻¹ = ((p : ℚ) - 1) / 12) :
    kirchhoffCount e = eisensteinNumerator p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_kirchhoffCount_eq_eisensteinNumerator_of_massFormula.solution
end ModularCurve
