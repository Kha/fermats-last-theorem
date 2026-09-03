import Definitions.Def_ModularCurve_ComponentGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_componentGroup_subsingleton

open ModularCurve
namespace ModularCurve
variable {ι : Type*} [Fintype ι]
theorem componentGroup_subsingleton (hι : Fintype.card ι ≤ 1) (e : ι → ℕ) :
    Subsingleton (componentGroup e) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_componentGroup_subsingleton.solution
end ModularCurve
