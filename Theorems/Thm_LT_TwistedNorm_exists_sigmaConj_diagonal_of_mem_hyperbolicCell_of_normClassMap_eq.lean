import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import P2M.Util
import P2M.Sol.S_LT_TwistedNorm_exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq

set_option autoImplicit false

theorem LT.TwistedNorm.exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ AutomorphicForm.hyperbolicCell F)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L)
    (h : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) L,
      ((g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g : Matrix.GeneralLinearGroup (Fin 2) L) :
          Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      ((g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g : Matrix.GeneralLinearGroup (Fin 2) L) :
          Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by p2m_exact_reverting @_root_.P2MW.S_LT_TwistedNorm_exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq.solution
