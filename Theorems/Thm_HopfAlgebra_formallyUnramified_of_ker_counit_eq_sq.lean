import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq

set_option autoImplicit false

universe u v

theorem HopfAlgebra.formallyUnramified_of_ker_counit_eq_sq
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    (hI : RingHom.ker (Bialgebra.counitAlgHom R H) = RingHom.ker (Bialgebra.counitAlgHom R H) ^ 2) :
    Algebra.FormallyUnramified R H := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq.solution
