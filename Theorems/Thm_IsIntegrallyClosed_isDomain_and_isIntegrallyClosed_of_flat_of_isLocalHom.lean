import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom

set_option autoImplicit false

universe u v

theorem IsIntegrallyClosed.isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsDomain S]
    [IsIntegrallyClosed S] (f : R →+* S) (hf : f.Flat) [IsLocalHom f] :
    IsDomain R ∧ IsIntegrallyClosed R := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom.solution
