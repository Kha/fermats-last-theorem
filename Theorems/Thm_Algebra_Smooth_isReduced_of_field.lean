import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Smooth_isReduced_of_field

set_option autoImplicit false

theorem Algebra.Smooth.isReduced_of_field
    (K R : Type) [Field K] [CommRing R] [Algebra K R] [Algebra.Smooth K R] :
    IsReduced R := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Smooth_isReduced_of_field.solution
