import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import P2M.Util
import P2M.Sol.S_ModularCurve_isAddCyclic_componentGroup_of_widths

open ModularCurve Finset Module
namespace ModularCurve
variable {ι : Type*} [Fintype ι]
theorem isAddCyclic_componentGroup_of_widths
    (e : ι → ℕ) (he : ∀ x, e x = 1 ∨ e x = 2 ∨ e x = 3)
    (h2 : ({x | e x = 2} : Set ι).Subsingleton)
    (h3 : ({x | e x = 3} : Set ι).Subsingleton) :
    IsAddCyclic (componentGroup e) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isAddCyclic_componentGroup_of_widths.solution
end ModularCurve
