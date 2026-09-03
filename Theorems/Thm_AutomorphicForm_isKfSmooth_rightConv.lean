import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isKfSmooth_rightConv

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel NumberField.AdelicHaar MeasureTheory
open AutomorphicForm

theorem AutomorphicForm.isKfSmooth_rightConv
    (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    IsKfSmooth F (rightConv F φ f) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isKfSmooth_rightConv.solution
