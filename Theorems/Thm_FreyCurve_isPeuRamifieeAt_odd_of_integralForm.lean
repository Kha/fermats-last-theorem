import Definitions.Def_WeierstrassCurve_PeuRamifiee
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyCurve_isPeuRamifieeAt_odd_of_integralForm

open FreyPackage
namespace FreyCurve
theorem isPeuRamifieeAt_odd_of_integralForm (P : FreyPackage) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) : P.freyCurve.IsPeuRamifieeAt P.p q := by p2m_exact_reverting @_root_.P2MW.S_FreyCurve_isPeuRamifieeAt_odd_of_integralForm.solution
end FreyCurve
