import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_canMap_surjective_of_surjective

theorem HopfAlgebra.canMap_surjective_of_surjective {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]
    {B : Type*} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Function.Surjective (HopfAlgebra.canMap π) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_canMap_surjective_of_surjective.solution
