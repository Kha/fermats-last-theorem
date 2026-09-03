import Definitions.Def_AutomorphicForm_WeylSelectors
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WeylIntegrable_rpow_Dy_le_translate_of_le
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec

set_option autoImplicit false

theorem AutomorphicForm.WeylIntegrable.rpow_Dy_le_translate_of_le (F : Type) [Field F] [NumberField F]
    (x u : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) {R : ℝ}
    (hu1 : ∀ w, ‖u.1 w‖ ≤ R)
    (hu2 : u.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (NumberField.RingOfIntegers F) F) {a : ℝ} (ha : 0 ≤ a) :
    Dy F x ^ (-a) ≤ ((1 + R) ^ (∑ w : NumberField.InfinitePlace F, w.mult)) ^ a * Dy F (x + u) ^ (-a) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WeylIntegrable_rpow_Dy_le_translate_of_le.solution
