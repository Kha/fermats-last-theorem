import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LT_TwistedNorm_exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mk_eq_mk_scalar_mul_unipotentGL2

set_option autoImplicit false

theorem LT.TwistedNorm.exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mk_eq_mk_scalar_mul_unipotentGL2
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    (∃ γ : Matrix.GeneralLinearGroup (Fin 2) F, γ ∈ AutomorphicForm.unipotentCell F ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) ↔
      ∃ (ζ : Lˣ) (b : L), Algebra.trace F L b ≠ 0 ∧
        LT.TwistedNorm.SigmaConjClasses.mk σ δ =
          LT.TwistedNorm.SigmaConjClasses.mk σ
            (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * AutomorphicForm.unipotentGL2 b) := by p2m_exact_reverting @_root_.P2MW.S_LT_TwistedNorm_exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mk_eq_mk_scalar_mul_unipotentGL2.solution
