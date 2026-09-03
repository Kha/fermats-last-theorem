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
import P2M.Sol.S_NumberField_exists_forall_card_le_mul_prod_of_forall_norm_eq_one_of_abs_log_norm_le

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem NumberField.exists_forall_card_le_mul_prod_of_forall_norm_eq_one_of_abs_log_norm_le
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (cinf : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : HeightOneSpectrum (𝓞 K) → ℝ), (∀ v, 0 ≤ c v) →
      ∀ (B : Finset K),
        (∀ x ∈ B, x ≠ 0 ∧
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ‖(algebraMap K (v.adicCompletion K) x)‖ = 1) ∧
          (∀ v ∈ S, |Real.log ‖(algebraMap K (v.adicCompletion K) x)‖| ≤ c v) ∧
          (∀ w : NumberField.InfinitePlace K, |Real.log (w x)| ≤ cinf)) →
        (B.card : ℝ) ≤ C * ∏ v ∈ S, (1 + c v) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_forall_card_le_mul_prod_of_forall_norm_eq_one_of_abs_log_norm_le.solution
