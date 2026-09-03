import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_ideleNorm_det_globalPoints

set_option autoImplicit false

open scoped NumberField

theorem AutomorphicForm.ideleNorm_det_globalPoints
    {F : Type} [Field F] [NumberField F] (γ : Matrix.GeneralLinearGroup (Fin 2) F) :
    NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 F) F γ)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_ideleNorm_det_globalPoints.solution
