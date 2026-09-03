import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_natCard_algHom_eq_mul_of_isHopfGalois

universe u v w x
theorem HopfAlgebra.natCard_algHom_eq_mul_of_isHopfGalois
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing B] [Bialgebra R B]
    [Module.Finite R A] (k : Type x) [Field k] [IsAlgClosed k] [Algebra R k]
    (π : A →ₐc[R] B) (hHG : HopfAlgebra.IsHopfGalois π) :
    Nat.card (A →ₐ[R] k) = Nat.card (B →ₐ[R] k) * Nat.card (↥(HopfAlgebra.hopfKer π) →ₐ[R] k) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_natCard_algHom_eq_mul_of_isHopfGalois.solution
