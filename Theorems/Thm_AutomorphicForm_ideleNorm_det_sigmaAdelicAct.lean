import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_ideleNorm_det_sigmaAdelicAct

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.ideleNorm_det_sigmaAdelicAct (F E : Type) [Field F] [Field E]
    [NumberField E] [Algebra F E] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E)
    (σ : E ≃ₐ[F] E) :
    ∀ x, NumberField.TateGlobal.ideleNorm E
        (Matrix.GeneralLinearGroup.det (sigmaAdelicAct F E D σ x)) =
      NumberField.TateGlobal.ideleNorm E (Matrix.GeneralLinearGroup.det x) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_ideleNorm_det_sigmaAdelicAct.solution
