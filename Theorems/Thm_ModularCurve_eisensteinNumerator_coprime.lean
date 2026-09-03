import Definitions.Def_ModularCurve_ModularUnit
import P2M.Util
import P2M.Sol.S_ModularCurve_eisensteinNumerator_coprime

open ModularCurve
namespace ModularCurve
theorem eisensteinNumerator_coprime (p : ℕ) (hp : p ≠ 0) : (eisensteinNumerator p).Coprime p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinNumerator_coprime.solution
end ModularCurve
