import Definitions.Def_ModularCurve_ComponentGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_gramMap_injective

open ModularCurve
namespace ModularCurve
variable {ι : Type*} [Fintype ι]
theorem gramMap_injective {e : ι → ℕ} (he : ∀ x, 0 < e x) :
    Function.Injective (gramMap e) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_gramMap_injective.solution
end ModularCurve
