import Definitions.Def_AutomorphicForm_WeylSelectors
import P2M.Util
namespace P2MW.S_AutomorphicForm_WeylIntegrable_Dy_pos

set_option autoImplicit false

open AutomorphicForm.WeylIntegrable in

theorem solution (F : Type) [Field F] [NumberField F]
    (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) : 0 < Dy F x := by
  rw [Dy]; exact_mod_cast MeasureTheory.distribHaarChar_pos
