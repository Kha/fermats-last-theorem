import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_normString_apply_eq_one_tmul_norm_apply_of_diagonal

set_option autoImplicit false

open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.normString_apply_eq_one_tmul_norm_apply_of_diagonal
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A]
    (δ : GL (Fin 2) (L ⊗[K] A))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0) :
    ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 ∧
    ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧
    ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 =
      (1 : L) ⊗ₜ[K] Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) ∧
    ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 =
      (1 : L) ⊗ₜ[K] Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_normString_apply_eq_one_tmul_norm_apply_of_diagonal.solution
