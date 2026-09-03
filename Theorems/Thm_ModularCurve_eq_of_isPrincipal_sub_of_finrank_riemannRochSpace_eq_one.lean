import Definitions.Def_ModularCurve_JZeroHeightForm
import P2M.Util
import P2M.Sol.S_ModularCurve_eq_of_isPrincipal_sub_of_finrank_riemannRochSpace_eq_one

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.eq_of_isPrincipal_sub_of_finrank_riemannRochSpace_eq_one (N : ℕ) [NeZero N]
    {D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (h1 : Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D) = 1)
    (hP : Divisor.IsPrincipal (D' - D)) : D' = D := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eq_of_isPrincipal_sub_of_finrank_riemannRochSpace_eq_one.solution
