import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isHopfGalois_of_surjective

universe u v w
theorem HopfAlgebra.isHopfGalois_of_surjective {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) : HopfAlgebra.IsHopfGalois π := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isHopfGalois_of_surjective.solution
