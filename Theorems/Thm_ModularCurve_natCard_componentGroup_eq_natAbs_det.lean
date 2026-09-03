import Definitions.Def_ModularCurve_ComponentGroupOrder
import P2M.Util
import P2M.Sol.S_ModularCurve_natCard_componentGroup_eq_natAbs_det

open ModularCurve
namespace ModularCurve
open Module
variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ] {e : ι → ℕ}
theorem natCard_componentGroup_eq_natAbs_det (he : ∀ x, 0 < e x)
    (c : Basis κ ℤ (characterLattice ι)) :
    Nat.card (componentGroup e) = ((gramMatrixOf e ⇑c).det).natAbs := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_natCard_componentGroup_eq_natAbs_det.solution
end ModularCurve
