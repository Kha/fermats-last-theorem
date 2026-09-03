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

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import P2M.Util
import P2M.Sol.S_NumberField_Idele_isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem
attribute [-simp] AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal
open scoped TensorProduct.RightActions in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in

theorem NumberField.Idele.isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (A : ∀ v : InfinitePlace K, Set (∀ w : v.Extension L, w.1.Completion)ˣ) (hA : ∀ v, IsCompact (A v))
    (Sf : Finset (HeightOneSpectrum (𝓞 K)))
    (B : ∀ v : HeightOneSpectrum (𝓞 K), Set (L ⊗[K] v.adicCompletion K)ˣ) (hB : ∀ v ∈ Sf, IsCompact (B v)) :
    IsCompact {t : (AdeleRing (𝓞 L) L)ˣ |
      (∀ v : InfinitePlace K, AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t ∈ A v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sf → AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ B v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
          AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v)} := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem.solution
