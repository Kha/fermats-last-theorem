import Mathlib
import Theorems.Thm_Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing
import P2M.Util
namespace P2MW.S_Algebra_Smooth_isReduced_of_field

set_option autoImplicit false

theorem solution
    (K R : Type) [Field K] [CommRing R] [Algebra K R] [Algebra.Smooth K R] :
    IsReduced R :=
  Algebra.Smooth.isReduced_of_isReduced_of_isNoetherianRing K R
