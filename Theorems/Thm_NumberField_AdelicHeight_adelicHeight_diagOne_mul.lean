import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHeight_adelicHeight_diagOne_mul
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight

theorem NumberField.AdelicHeight.adelicHeight_diagOne_mul
    (F : Type) [Field F] [NumberField F] (a : (AdeleRing (𝓞 F) F)ˣ) (h : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (diagOne a * h) = ideleNorm F a * adelicHeight F h := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHeight_adelicHeight_diagOne_mul.solution
