import Mathlib
import P2M.Util
namespace P2MW.S_IntermediateField_exists_mulEquiv_fixedField_apply_eq

set_option autoImplicit false

theorem solution
    (E F : Type) [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F] (H : Subgroup (F ≃ₐ[E] F)) :
    ∃ Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F), ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y := by
  refine ⟨(MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H).symm).trans
    (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)), fun s y => ?_⟩
  rfl
