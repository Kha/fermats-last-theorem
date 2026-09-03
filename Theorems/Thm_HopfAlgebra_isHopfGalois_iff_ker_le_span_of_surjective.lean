import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective

universe u v w

theorem HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Flat R A]
    {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    HopfAlgebra.IsHopfGalois π ↔
      RingHom.ker (π : A →ₐ[R] B) ≤
        Ideal.span {a : A | a ∈ HopfAlgebra.hopfKer π ∧ Coalgebra.counit (R := R) a = 0} := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective.solution
