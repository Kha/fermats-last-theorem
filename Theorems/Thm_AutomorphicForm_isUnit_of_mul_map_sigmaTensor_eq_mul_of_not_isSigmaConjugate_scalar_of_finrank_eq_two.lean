import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

open scoped TensorProduct

theorem AutomorphicForm.isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [Field A] [Algebra K A]
    (c : Aˣ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] A)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (hy : y ≠ 0)
    (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hyk : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * y.map (AutomorphicForm.sigmaTensor K L A σ) =
      y * k) :
    IsUnit y := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.solution
