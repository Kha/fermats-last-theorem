import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_lt

set_option autoImplicit false

universe u

theorem ProjSpaceCech.Twist.subsingleton_cohomology_of_lt (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) {i : ℕ}
    (hi : n < i) : Subsingleton (ProjSpaceCech.Twist.H R n d i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_lt.solution
