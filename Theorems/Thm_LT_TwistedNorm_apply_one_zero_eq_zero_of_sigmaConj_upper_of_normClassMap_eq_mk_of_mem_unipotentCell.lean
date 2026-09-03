import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import P2M.Util
import P2M.Sol.S_LT_TwistedNorm_apply_one_zero_eq_zero_of_sigmaConj_upper_of_normClassMap_eq_mk_of_mem_unipotentCell

set_option autoImplicit false

theorem LT.TwistedNorm.apply_one_zero_eq_zero_of_sigmaConj_upper_of_normClassMap_eq_mk_of_mem_unipotentCell
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (β : Matrix.GeneralLinearGroup (Fin 2) L) (hβ : (β : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ AutomorphicForm.unipotentCell F)
    (hclass : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ β) = ConjClasses.mk γ)
    (η : Matrix.GeneralLinearGroup (Fin 2) L)
    (hη : ((η⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) η :
        Matrix.GeneralLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((η : Matrix.GeneralLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by p2m_exact_reverting @_root_.P2MW.S_LT_TwistedNorm_apply_one_zero_eq_zero_of_sigmaConj_upper_of_normClassMap_eq_mk_of_mem_unipotentCell.solution
