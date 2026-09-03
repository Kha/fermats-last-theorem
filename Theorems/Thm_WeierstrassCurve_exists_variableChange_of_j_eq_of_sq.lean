import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Tactic.LinearCombination
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_of_j_eq_of_sq

namespace WeierstrassCurve
variable {F : Type*} [Field F]
theorem exists_variableChange_of_j_eq_of_sq
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]
    (heq : E.j = E'.j) (hj0 : E.j ≠ 0) (hj1728 : E.j ≠ 1728)
    {s : F} (hs : s ^ 2 = E.c₆ * E'.c₄ / (E'.c₆ * E.c₄)) :
    ∃ C : VariableChange F, C • E = E' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_of_j_eq_of_sq.solution
end WeierstrassCurve
