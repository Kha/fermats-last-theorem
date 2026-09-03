import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_of_isShortNF_of_sq

namespace WeierstrassCurve
variable {F : Type*} [Field F]
theorem exists_variableChange_of_isShortNF_of_sq (E E' : WeierstrassCurve F)
    [E.IsShortNF] [E'.IsShortNF]
    (ha₄ : E.a₄ ≠ 0) (ha₆ : E.a₆ ≠ 0) (ha₄' : E'.a₄ ≠ 0) (ha₆' : E'.a₆ ≠ 0)
    (hrel : E.a₄ ^ 3 * E'.a₆ ^ 2 = E'.a₄ ^ 3 * E.a₆ ^ 2)
    {s : F} (hs : s ^ 2 * (E'.a₆ * E.a₄) = E.a₆ * E'.a₄) :
    ∃ C : VariableChange F, C • E = E' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_of_isShortNF_of_sq.solution
end WeierstrassCurve
