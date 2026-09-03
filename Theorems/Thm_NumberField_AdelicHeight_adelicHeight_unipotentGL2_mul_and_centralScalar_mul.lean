import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul

set_option autoImplicit false

open AutomorphicForm NumberField

theorem NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul
    (F : Type) [Field F] [NumberField F] :
    (∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
        adelicHeight F (unipotentGL2 x * g) = adelicHeight F g) ∧
      ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
        adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul.solution
