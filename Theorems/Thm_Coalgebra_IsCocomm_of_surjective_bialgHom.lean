import Mathlib
import P2M.Util
import P2M.Sol.S_Coalgebra_IsCocomm_of_surjective_bialgHom
set_option autoImplicit false
open scoped TensorProduct
theorem Coalgebra.IsCocomm.of_surjective_bialgHom
    {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
    {B : Type*} [Semiring B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Coalgebra.IsCocomm R B := by p2m_exact_reverting @_root_.P2MW.S_Coalgebra_IsCocomm_of_surjective_bialgHom.solution
