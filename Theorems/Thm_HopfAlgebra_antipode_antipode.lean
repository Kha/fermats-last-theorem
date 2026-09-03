import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_antipode_antipode

theorem HopfAlgebra.antipode_antipode {R : Type*} [CommSemiring R]
    {A : Type*} [CommSemiring A] [HopfAlgebra R A] (a : A) :
    HopfAlgebra.antipode R (HopfAlgebra.antipode R a) = a := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_antipode_antipode.solution
