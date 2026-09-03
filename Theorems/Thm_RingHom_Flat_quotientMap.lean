import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_Flat_quotientMap

set_option autoImplicit false
theorem RingHom.Flat.quotientMap
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat) (I : Ideal R) :
    (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).Flat := by p2m_exact_reverting @_root_.P2MW.S_RingHom_Flat_quotientMap.solution
