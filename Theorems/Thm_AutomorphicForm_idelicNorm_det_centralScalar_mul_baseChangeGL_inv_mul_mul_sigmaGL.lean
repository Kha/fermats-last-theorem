import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_idelicNorm_det_centralScalar_mul_baseChangeGL_inv_mul_mul_sigmaGL

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.idelicNorm_det_centralScalar_mul_baseChangeGL_inv_mul_mul_sigmaGL
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (w : (AdeleRing (𝓞 L) L)ˣ) (δ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
        (Matrix.GeneralLinearGroup.det
          (AutomorphicForm.centralScalar (𝓞 L) L w *
            AutomorphicForm.baseChangeGL K L (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x))) =
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w ^ 2 *
        (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
          (Matrix.GeneralLinearGroup.det (AutomorphicForm.baseChangeGL K L δ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_idelicNorm_det_centralScalar_mul_baseChangeGL_inv_mul_mul_sigmaGL.solution
