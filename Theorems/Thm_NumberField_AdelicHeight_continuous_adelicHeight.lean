import Definitions.Def_NumberField_AdelicHeight
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHeight_continuous_adelicHeight

open NumberField NumberField.AdelicHeight AutomorphicForm

theorem NumberField.AdelicHeight.continuous_adelicHeight
    (F : Type) [Field F] [NumberField F] : Continuous (adelicHeight F) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHeight_continuous_adelicHeight.solution
