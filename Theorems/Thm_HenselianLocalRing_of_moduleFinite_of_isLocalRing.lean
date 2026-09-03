import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_of_moduleFinite_of_isLocalRing

set_option autoImplicit false

universe u v

theorem HenselianLocalRing.of_moduleFinite_of_isLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S] :
    HenselianLocalRing S := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_of_moduleFinite_of_isLocalRing.solution
