import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import P2M.Util
import P2M.Sol.S_ModularCurve_natCard_componentGroup_eq_natAbs_det_diffChar

open ModularCurve Module
namespace ModularCurve
open Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ] {e : ι → ℕ}
theorem natCard_componentGroup_eq_natAbs_det_diffChar (he : ∀ x, 0 < e x)
    (σ : Option κ ≃ ι) :
    Nat.card (componentGroup e) = ((gramMatrixOf e (diffChar σ)).det).natAbs := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_natCard_componentGroup_eq_natAbs_det_diffChar.solution
end ModularCurve
