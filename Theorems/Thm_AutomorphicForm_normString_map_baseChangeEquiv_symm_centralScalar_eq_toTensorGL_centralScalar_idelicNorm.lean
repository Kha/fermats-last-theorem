import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_normString_map_baseChangeEquiv_symm_centralScalar_eq_toTensorGL_centralScalar_idelicNorm

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.normString_map_baseChangeEquiv_symm_centralScalar_eq_toTensorGL_centralScalar_idelicNorm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (w : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).symm.toRingHom
          (AutomorphicForm.centralScalar (𝓞 L) L w)) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
        (AutomorphicForm.centralScalar (𝓞 K) K ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_normString_map_baseChangeEquiv_symm_centralScalar_eq_toTensorGL_centralScalar_idelicNorm.solution
