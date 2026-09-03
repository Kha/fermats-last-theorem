import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_exists_one_tmul_eq_of_map_eq_and_exists_units_eq_map_mul_inv_of_prod_iterate_map_eq_one

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.TensorProduct.exists_one_tmul_eq_of_map_eq_and_exists_units_eq_map_mul_inv_of_prod_iterate_map_eq_one
    (K L F : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Field F] [Algebra K F]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ z : L ⊗[K] F, Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F) z = z →
      ∃ f : F, (1 : L) ⊗ₜ[K] f = z) ∧
    (∀ x : L ⊗[K] F,
      ((List.range (Module.finrank K L)).map fun i =>
          (⇑(Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F)))^[i] x).prod = 1 →
      ∃ y : (L ⊗[K] F)ˣ,
        x = Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F) (y : L ⊗[K] F) * ↑y⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_exists_one_tmul_eq_of_map_eq_and_exists_units_eq_map_mul_inv_of_prod_iterate_map_eq_one.solution
