import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteAlong_heckeAlphaOneBar_of_neZero

set_option autoImplicit false

theorem ModularCurve.finiteAlong_heckeAlphaOneBar_of_neZero (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ] :
    AlgebraicCurve.FiniteAlong L (ModularCurve.heckeAlphaOneBar L N ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteAlong_heckeAlphaOneBar_of_neZero.solution
