import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_sigmaTensor_twistedResolvent_sub_mul_eq_one_sub_norm_smul_and_twistedResolvent_sigmaTensor_sub_mul_eq

set_option autoImplicit false

open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.sigmaTensor_twistedResolvent_sub_mul_eq_one_sub_norm_smul_and_twistedResolvent_sigmaTensor_sub_mul_eq
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A] (r y : (L ⊗[K] A)) :
    (AutomorphicForm.sigmaTensor K L A σ
        (∑ j ∈ Finset.range (Module.finrank K L),
          (∏ i ∈ Finset.range j, (AutomorphicForm.sigmaTensor K L A σ.symm)^[i + 1] r) * (AutomorphicForm.sigmaTensor K L A σ.symm)^[j + 1] y) -
      r * (∑ j ∈ Finset.range (Module.finrank K L),
          (∏ i ∈ Finset.range j, (AutomorphicForm.sigmaTensor K L A σ.symm)^[i + 1] r) * (AutomorphicForm.sigmaTensor K L A σ.symm)^[j + 1] y) =
      algebraMap A (L ⊗[K] A) (1 - Algebra.norm A r) * y) ∧
    ((∑ j ∈ Finset.range (Module.finrank K L),
          (∏ i ∈ Finset.range j, (AutomorphicForm.sigmaTensor K L A σ.symm)^[i + 1] r) * (AutomorphicForm.sigmaTensor K L A σ.symm)^[j + 1] (AutomorphicForm.sigmaTensor K L A σ y - r * y)) =
      algebraMap A (L ⊗[K] A) (1 - Algebra.norm A r) * y) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_sigmaTensor_twistedResolvent_sub_mul_eq_one_sub_norm_smul_and_twistedResolvent_sigmaTensor_sub_mul_eq.solution
