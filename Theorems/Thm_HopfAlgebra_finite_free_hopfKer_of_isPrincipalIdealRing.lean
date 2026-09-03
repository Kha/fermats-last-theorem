import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing

universe u v w
theorem HopfAlgebra.finite_free_hopfKer_of_isPrincipalIdealRing {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
    {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) :
    Module.Finite R ↥(HopfAlgebra.hopfKer π) ∧ Module.Free R ↥(HopfAlgebra.hopfKer π) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing.solution
