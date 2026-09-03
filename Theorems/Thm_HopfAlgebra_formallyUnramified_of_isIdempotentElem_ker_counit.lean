import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_formallyUnramified_of_isIdempotentElem_ker_counit

set_option autoImplicit false

universe u v

theorem HopfAlgebra.formallyUnramified_of_isIdempotentElem_ker_counit
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    (hI : IsIdempotentElem (RingHom.ker (Bialgebra.counitAlgHom R A))) :
    Algebra.FormallyUnramified R A := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_formallyUnramified_of_isIdempotentElem_ker_counit.solution
