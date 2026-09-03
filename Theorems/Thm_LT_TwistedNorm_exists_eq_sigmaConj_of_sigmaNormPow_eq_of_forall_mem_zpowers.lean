import Definitions.Def_TwistedNormClasses
import P2M.Util
import P2M.Sol.S_LT_TwistedNorm_exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers

theorem LT.TwistedNorm.exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {δ₁ δ₂ : Matrix.GeneralLinearGroup (Fin 2) L}
    (hN : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ₁
      = LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ₂) :
    ∃ h : Matrix.GeneralLinearGroup (Fin 2) L, δ₂ = h⁻¹ * δ₁ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h
 := by p2m_exact_reverting @_root_.P2MW.S_LT_TwistedNorm_exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers.solution
