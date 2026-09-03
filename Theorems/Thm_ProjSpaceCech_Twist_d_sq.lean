import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_Twist_d_sq

set_option autoImplicit false

universe u

theorem ProjSpaceCech.Twist.d_sq (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (i : ℕ) :
    ProjSpaceCech.Twist.d R n d (i + 1) ∘ₗ ProjSpaceCech.Twist.d R n d i = 0 := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_Twist_d_sq.solution
