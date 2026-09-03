import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined

set_option autoImplicit false

theorem ModularCurve.finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined (L : Type*) [Field L]
    [Algebra ℚ L] (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ]
    (h : ModularCurve.HeckeBetaOneDefined N ℓ) :
    AlgebraicCurve.FiniteAlong L (ModularCurve.heckeBetaOneBar L N ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined.solution
