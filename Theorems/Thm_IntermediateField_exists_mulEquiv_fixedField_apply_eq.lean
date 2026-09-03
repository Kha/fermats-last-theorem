import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_mulEquiv_fixedField_apply_eq

set_option autoImplicit false

theorem IntermediateField.exists_mulEquiv_fixedField_apply_eq
    (E F : Type) [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F] (H : Subgroup (F ≃ₐ[E] F)) :
    ∃ Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F), ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_mulEquiv_fixedField_apply_eq.solution
