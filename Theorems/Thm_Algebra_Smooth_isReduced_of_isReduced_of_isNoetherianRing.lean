import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing

set_option autoImplicit false

universe u

theorem Algebra.Smooth.isReduced_of_isReduced_of_isNoetherianRing
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    [IsReduced R] [IsNoetherianRing R] : IsReduced S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing.solution
