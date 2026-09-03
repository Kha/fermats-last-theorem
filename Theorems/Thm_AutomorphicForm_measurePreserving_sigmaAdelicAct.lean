import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_measurePreserving_sigmaAdelicAct
attribute [-simp] FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.measurePreserving_sigmaAdelicAct (F E : Type) [Field F] [Field E]
    [NumberField E] [Algebra F E] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E)
    (σ : E ≃ₐ[F] E) :
    MeasurePreserving (sigmaAdelicAct F E D σ) (adelicGLHaar (Fin 2) (𝓞 E) E)
      (adelicGLHaar (Fin 2) (𝓞 E) E) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_measurePreserving_sigmaAdelicAct.solution
