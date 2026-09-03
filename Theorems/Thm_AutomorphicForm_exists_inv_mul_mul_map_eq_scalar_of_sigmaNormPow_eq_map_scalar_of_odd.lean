import Definitions.Def_TwistedNormClasses
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_inv_mul_mul_map_eq_scalar_of_sigmaNormPow_eq_map_scalar_of_odd

set_option autoImplicit false

theorem AutomorphicForm.exists_inv_mul_mul_map_eq_scalar_of_sigmaNormPow_eq_map_scalar_of_odd
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hodd : Odd (Module.finrank K L))
    (δ : GL (Fin 2) L) (b : Kˣ)
    (hb : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L))
        (Module.finrank K L) δ =
      Matrix.GeneralLinearGroup.map (algebraMap K L) (Matrix.GeneralLinearGroup.scalar (Fin 2) b)) :
    ∃ (h : GL (Fin 2) L) (d : Lˣ),
      h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h =
        Matrix.GeneralLinearGroup.scalar (Fin 2) d := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_inv_mul_mul_map_eq_scalar_of_sigmaNormPow_eq_map_scalar_of_odd.solution
