import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_linearMap_apply_eq_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm_of_infinite

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_linearMap_apply_eq_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm_of_infinite
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Infinite K]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A] (a b : L ⊗[K] A) :
    ∃ T : (L ⊗[K] A) →ₗ[A] (L ⊗[K] A),
      (∀ y : L ⊗[K] A, T y = a * AutomorphicForm.sigmaTensor K L A σ y - b * y) ∧
      LinearMap.det T = (-1) ^ Module.finrank K L * (Algebra.norm A b - Algebra.norm A a) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_linearMap_apply_eq_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm_of_infinite.solution
