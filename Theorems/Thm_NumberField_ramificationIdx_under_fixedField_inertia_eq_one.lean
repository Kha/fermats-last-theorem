import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_ramificationIdx_under_fixedField_inertia_eq_one

set_option autoImplicit false

open NumberField

theorem NumberField.ramificationIdx_under_fixedField_inertia_eq_one
    (F : Type) [Field F] [NumberField F]
    (M : Type) [Field M] [NumberField M] [Algebra F M] [IsGalois F M]
    (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (E : IntermediateField F M) (hE : E = IntermediateField.fixedField (Q.inertia (M ≃ₐ[F] M))) :
    (Q.under (𝓞 F)).ramificationIdx' (Q.under (𝓞 ↥E)) = 1 ∧
      (Q.under (𝓞 ↥E)).ramificationIdx' Q = (Q.under (𝓞 F)).ramificationIdx' Q := by p2m_exact_reverting @_root_.P2MW.S_NumberField_ramificationIdx_under_fixedField_inertia_eq_one.solution
