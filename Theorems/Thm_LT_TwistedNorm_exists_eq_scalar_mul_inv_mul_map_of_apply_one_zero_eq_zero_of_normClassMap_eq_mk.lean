import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import P2M.Util
import P2M.Sol.S_LT_TwistedNorm_exists_eq_scalar_mul_inv_mul_map_of_apply_one_zero_eq_zero_of_normClassMap_eq_mk

set_option autoImplicit false

theorem LT.TwistedNorm.exists_eq_scalar_mul_inv_mul_map_of_apply_one_zero_eq_zero_of_normClassMap_eq_mk
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [Infinite F]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L) (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (hγ : γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F)
    (hN : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) :
    ∃ (h : Matrix.GeneralLinearGroup (Fin 2) L) (u : Lˣ),
      δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
        (h⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) := by p2m_exact_reverting @_root_.P2MW.S_LT_TwistedNorm_exists_eq_scalar_mul_inv_mul_map_of_apply_one_zero_eq_zero_of_normClassMap_eq_mk.solution
