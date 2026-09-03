import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_Twist_finite_cohomology

set_option autoImplicit false

universe u

theorem ProjSpaceCech.Twist.finite_cohomology (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (i : ℕ) :
    Module.Finite R (ProjSpaceCech.Twist.H R n d i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_Twist_finite_cohomology.solution
