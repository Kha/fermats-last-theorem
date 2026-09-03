import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LT_TwistedNorm_exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mul_eq_mul_map_and_trace_ne_zero_of_apply_one_zero_eq_zero

set_option autoImplicit false

theorem LT.TwistedNorm.exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mul_eq_mul_map_and_trace_ne_zero_of_apply_one_zero_eq_zero
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L) (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (∃ γ : Matrix.GeneralLinearGroup (Fin 2) F, γ ∈ AutomorphicForm.unipotentCell F ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) ↔
      ∃ r : L, r ≠ 0 ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 0 0 * r = (δ : Matrix (Fin 2) (Fin 2) L) 1 1 * σ r ∧
        Algebra.trace F L (r * (δ : Matrix (Fin 2) (Fin 2) L) 0 1 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LT_TwistedNorm_exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mul_eq_mul_map_and_trace_ne_zero_of_apply_one_zero_eq_zero.solution
