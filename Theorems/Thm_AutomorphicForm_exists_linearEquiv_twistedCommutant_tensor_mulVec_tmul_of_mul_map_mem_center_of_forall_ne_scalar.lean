import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_linearEquiv_twistedCommutant_tensor_mulVec_tmul_of_mul_map_mem_center_of_forall_ne_scalar

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_linearEquiv_twistedCommutant_tensor_mulVec_tmul_of_mul_map_mem_center_of_forall_ne_scalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    (hδ₀ : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ ∈ Subgroup.center (GL (Fin 2) L))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (b : Fin 2 → L) (hb : b ≠ 0)
    (A : Type) [CommRing A] [Algebra K A] :
    ∃ (DA : Submodule A (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)))
      (e : DA ≃ₗ[A] (Fin 2 → L ⊗[K] A)),
      (DA : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) = {x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) |
        x * ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ :
                GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
          ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ :
                GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
            x.map (AutomorphicForm.sigmaTensor K L A σ)} ∧
      ∀ x : DA, e x = (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).mulVec (fun i => b i ⊗ₜ[K] 1) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_linearEquiv_twistedCommutant_tensor_mulVec_tmul_of_mul_map_mem_center_of_forall_ne_scalar.solution
