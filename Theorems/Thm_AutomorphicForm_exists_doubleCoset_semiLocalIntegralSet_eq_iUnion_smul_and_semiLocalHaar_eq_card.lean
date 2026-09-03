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
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_doubleCoset_semiLocalIntegralSet_eq_iUnion_smul_and_semiLocalHaar_eq_card

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_doubleCoset_semiLocalIntegralSet_eq_iUnion_smul_and_semiLocalHaar_eq_card
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ∃ (m : ℕ) (k : Fin m → GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      (∀ i, k i ∈ semiLocalIntegralSet K L v) ∧
      semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v =
        ⋃ i, k i • (a • semiLocalIntegralSet K L v) ∧
      (∀ i j, i ≠ j → Disjoint (k i • (a • semiLocalIntegralSet K L v)) (k j • (a • semiLocalIntegralSet K L v))) ∧
      AutomorphicForm.semiLocalHaar K L v (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) = m := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_doubleCoset_semiLocalIntegralSet_eq_iUnion_smul_and_semiLocalHaar_eq_card.solution
