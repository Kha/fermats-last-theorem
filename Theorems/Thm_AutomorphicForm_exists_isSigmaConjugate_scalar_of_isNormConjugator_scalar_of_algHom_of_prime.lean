import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime

set_option autoImplicit false

open AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A] (ι : L →ₐ[K] A)
    (c : Aˣ) (δ y : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormConjugator K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    ∃ z : (L ⊗[K] A)ˣ,
      AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime.solution
