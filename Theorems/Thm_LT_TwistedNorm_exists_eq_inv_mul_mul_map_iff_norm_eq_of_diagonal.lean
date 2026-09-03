import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import P2M.Util
import P2M.Sol.S_LT_TwistedNorm_exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal

set_option autoImplicit false

theorem LT.TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (t t' : GL (Fin 2) L)
    (ht : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) (ht' : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    ((∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ t' = b⁻¹ * t * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ↔
      Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧ Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ∧
    ((∃ a : GL (Fin 2) L, ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧ t' = a⁻¹ * t * Matrix.GeneralLinearGroup.map (σ : L →+* L) a) ↔
      Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧ Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ∧
    ((∃ g : GL (Fin 2) L, t' = g⁻¹ * t * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ↔
      (Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧ Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ∨
      (Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ∧ Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0))) := by p2m_exact_reverting @_root_.P2MW.S_LT_TwistedNorm_exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal.solution
