import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_eq_of_infinite_setOf_equation

theorem WeierstrassCurve.eq_of_infinite_setOf_equation
    {F : Type*} [Field F] {W V : WeierstrassCurve F}
    (h : {xy : F × F | W.toAffine.Equation xy.1 xy.2 ∧ V.toAffine.Equation xy.1 xy.2}.Infinite) :
    W = V := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_eq_of_infinite_setOf_equation.solution
