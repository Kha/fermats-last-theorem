import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_natCard_algHom_eq_mul_of_surjective

universe u v w x
theorem HopfAlgebra.natCard_algHom_eq_mul_of_surjective {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) (k : Type x) [Field k] [IsAlgClosed k] [Algebra R k] :
    Nat.card (A →ₐ[R] k) = Nat.card (B →ₐ[R] k) * Nat.card (↥(HopfAlgebra.hopfKer π) →ₐ[R] k) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_natCard_algHom_eq_mul_of_surjective.solution
