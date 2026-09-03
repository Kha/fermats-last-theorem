import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective

set_option autoImplicit false

universe u v w

theorem HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
    {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    (∃ r : A →ₗ[↥(HopfAlgebra.hopfKer π)] ↥(HopfAlgebra.hopfKer π),
        ∀ c : ↥(HopfAlgebra.hopfKer π), r (c : A) = c) ∧
      Module.Finite R ↥(HopfAlgebra.hopfKer π) ∧ Module.Projective R ↥(HopfAlgebra.hopfKer π) ∧
      ∀ 𝔭 : PrimeSpectrum R,
        Module.rankAtStalk (R := R) ↥(HopfAlgebra.hopfKer π) 𝔭 * Module.finrank R B =
          Module.finrank R A := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective.solution
