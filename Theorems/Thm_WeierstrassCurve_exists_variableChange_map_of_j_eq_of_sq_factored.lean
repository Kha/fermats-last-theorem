import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_map_of_j_eq_of_sq_factored

namespace WeierstrassCurve
theorem exists_variableChange_map_of_j_eq_of_sq_factored
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (E E' : WeierstrassCurve K) [E.IsElliptic] [E'.IsElliptic]
    (heq : E.j = E'.j) (hj0 : E.j ≠ 0) (hj1728 : E.j ≠ 1728)
    {s : L} (hs : s ^ 2 = f (E.c₆ * E'.c₄ / (E'.c₆ * E.c₄))) :
    ∃ (A B : VariableChange K) (hs0 : s ≠ 0),
      ((A.map f) * (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange L) * (B.map f)) • E.map f
        = E'.map f := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_map_of_j_eq_of_sq_factored.solution
end WeierstrassCurve
