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
import P2M.Sol.S_AutomorphicForm_norm_tensorPlace_apply_eq_algebraMap_norm_of_baseChangeGL_eq_globalPoints

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.norm_tensorPlace_apply_eq_algebraMap_norm_of_baseChangeGL_eq_globalPoints
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (t : GL (Fin 2) L) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t) (i j : Fin 2) :
    (∀ v : HeightOneSpectrum (𝓞 K),
      Algebra.norm (v.adicCompletion K)
          ((AutomorphicForm.tensorPlace K L v δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) =
        algebraMap K (v.adicCompletion K) (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) i j))) ∧
    Algebra.norm (InfiniteAdeleRing K)
        ((AutomorphicForm.tensorArch K L δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i j) =
      algebraMap K (InfiniteAdeleRing K) (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) i j)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_norm_tensorPlace_apply_eq_algebraMap_norm_of_baseChangeGL_eq_globalPoints.solution
