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
import P2M.Sol.S_AutomorphicForm_exists_glArch_eq_one_and_semiLocalComponent_glFin_eq_of_mem_semiLocalIntegralSet

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_glArch_eq_one_and_semiLocalComponent_glFin_eq_of_mem_semiLocalIntegralSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (k : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hk : k ∈ semiLocalIntegralSet K L v) :
    ∃ g : AdelicGL2 (𝓞 L) L,
      NumberField.AdelicLevel.glArch (𝓞 L) L g = 1 ∧
      NumberField.AdelicLevel.glFin (𝓞 L) L g ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 L) L ∧
      semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L g) = k ∧
      ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v →
        semiLocalComponent K L v' (NumberField.AdelicLevel.glFin (𝓞 L) L g) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_glArch_eq_one_and_semiLocalComponent_glFin_eq_of_mem_semiLocalIntegralSet.solution
