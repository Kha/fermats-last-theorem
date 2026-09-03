import Definitions.Def_AutomorphicForm_WeylSelectors
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WeylIntegrable_Dy_eq_prod_mul_relIndex
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec

set_option autoImplicit false

theorem AutomorphicForm.WeylIntegrable.Dy_eq_prod_mul_relIndex (F : Type) [Field F] [NumberField F]
    (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) :
    Dy F x = (∏ w : NumberField.InfinitePlace F, (max 1 ‖x.1 w‖) ^ w.mult)
      * ((intLattice F).relIndex (dilate F (finPart F (yUnit (selRel F x.1 x.2)))) : ℝ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WeylIntegrable_Dy_eq_prod_mul_relIndex.solution
