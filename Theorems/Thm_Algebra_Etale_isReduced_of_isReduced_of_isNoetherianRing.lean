import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing

universe u

theorem Algebra.Etale.isReduced_of_isReduced_of_isNoetherianRing
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [_root_.IsReduced R] [Algebra.Etale R S] :
    _root_.IsReduced S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing.solution
