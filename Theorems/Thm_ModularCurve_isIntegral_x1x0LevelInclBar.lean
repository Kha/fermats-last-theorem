import Mathlib
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegral_x1x0LevelInclBar

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve~finiteAlong_x1x0LevelInclBar"

theorem ModularCurve.isIntegral_x1x0LevelInclBar (L : Type*) [Field L] [Algebra ℚ L]
    {N N' : ℕ} [NeZero N] [NeZero N'] (t : ℕ) (h : N * t ∣ N') :
    (x1x0LevelInclBar L t h).toRingHom.IsIntegral := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegral_x1x0LevelInclBar.solution
