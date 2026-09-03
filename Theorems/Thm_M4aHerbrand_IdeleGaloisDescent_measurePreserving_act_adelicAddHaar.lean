import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_M4aHerbrand_IdeleGaloisDescent_measurePreserving_act_adelicAddHaar
attribute [-simp] FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem M4aHerbrand.IdeleGaloisDescent.measurePreserving_act_adelicAddHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    MeasurePreserving (D.act σ) (adelicAddHaar (𝓞 L) L) (adelicAddHaar (𝓞 L) L) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_IdeleGaloisDescent_measurePreserving_act_adelicAddHaar.solution
