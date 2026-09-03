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
import P2M.Sol.S_AutomorphicForm_normString_tensorArch_eq_toTensorGL_diagUnits2_of_baseChangeGL_eq_globalPoints

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.normString_tensorArch_eq_toTensorGL_diagUnits2_of_baseChangeGL_eq_globalPoints
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t)
    (hα : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ 0)
    (hβ : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0) :
    AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ) =
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
        (diagUnits2
          (Units.map (algebraMap K (InfiniteAdeleRing K) : K →* InfiniteAdeleRing K)
            (Units.mk0 _ hα))
          (Units.map (algebraMap K (InfiniteAdeleRing K) : K →* InfiniteAdeleRing K)
            (Units.mk0 _ hβ))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_normString_tensorArch_eq_toTensorGL_diagUnits2_of_baseChangeGL_eq_globalPoints.solution
