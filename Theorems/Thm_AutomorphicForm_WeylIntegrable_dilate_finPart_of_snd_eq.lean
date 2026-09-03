import Definitions.Def_AutomorphicForm_WeylSelectors
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WeylIntegrable_dilate_finPart_of_snd_eq

set_option autoImplicit false

theorem AutomorphicForm.WeylIntegrable.dilate_finPart_of_snd_eq (F : Type) [Field F] [NumberField F]
    (x y : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) (hy2 : y.2 = x.2) :
    dilate F (finPart F (yUnit (selRel F y.1 y.2))) = dilate F (finPart F (yUnit (selRel F x.1 x.2))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WeylIntegrable_dilate_finPart_of_snd_eq.solution
