import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_isLocalRing_of_isDomain_of_moduleFinite

set_option autoImplicit false

universe u v

theorem HenselianLocalRing.isLocalRing_of_isDomain_of_moduleFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_isLocalRing_of_isDomain_of_moduleFinite.solution
