import Mathlib
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteAlong_x1x0LevelInclBar

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.finiteAlong_x1x0LevelInclBar (L : Type*) [Field L] [Algebra ℚ L]
    {N N' : ℕ} [NeZero N] [NeZero N'] (t : ℕ) (h : N * t ∣ N') :
    FiniteAlong L (x1x0LevelInclBar L t h) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteAlong_x1x0LevelInclBar.solution
