import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.smoothOfRelativeDimension_torusStr
    (S : Type u) [CommRing S] (d : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension d S (torusCoord S d) ∧
      SmoothOfRelativeDimension d (torusStr S d) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr.solution
