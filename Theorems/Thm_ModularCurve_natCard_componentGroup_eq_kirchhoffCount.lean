import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import P2M.Util
import P2M.Sol.S_ModularCurve_natCard_componentGroup_eq_kirchhoffCount

open ModularCurve
namespace ModularCurve
open Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → ℕ}
theorem natCard_componentGroup_eq_kirchhoffCount [Nonempty ι] (he : ∀ x, 0 < e x) :
    Nat.card (componentGroup e) = kirchhoffCount e := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_natCard_componentGroup_eq_kirchhoffCount.solution
end ModularCurve
