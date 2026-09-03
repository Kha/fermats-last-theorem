import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_nonempty_algEquiv_tensor_quotient_of_isScalarTower

open scoped TensorProduct

theorem Algebra.TensorProduct.nonempty_algEquiv_tensor_quotient_of_isScalarTower
    (Λ : Type*) [CommRing Λ] (I : Ideal Λ) (k : Type*) [CommRing k] [Algebra Λ k]
    [Algebra (Λ ⧸ I) k] [IsScalarTower Λ (Λ ⧸ I) k]
    (A : Type*) [CommRing A] [Algebra Λ A] :
    Nonempty (k ⊗[Λ] A ≃ₐ[k] k ⊗[Λ ⧸ I] (A ⧸ I.map (algebraMap Λ A))) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_nonempty_algEquiv_tensor_quotient_of_isScalarTower.solution
