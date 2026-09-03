import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mem_twistedCentralizer_iff_of_diagonal_of_isUnit_norm_sub_norm

set_option autoImplicit false

open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.mem_twistedCentralizer_iff_of_diagonal_of_isUnit_norm_sub_norm
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A]
    (δ : GL (Fin 2) (L ⊗[K] A))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0)
    (hN : IsUnit (Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) -
      Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1)))
    (t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ ↔
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧
        (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 ∈
          Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) ∧
        (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 ∈
          Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mem_twistedCentralizer_iff_of_diagonal_of_isUnit_norm_sub_norm.solution
