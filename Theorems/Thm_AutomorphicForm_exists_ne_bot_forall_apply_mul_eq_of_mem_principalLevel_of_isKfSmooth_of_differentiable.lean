import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_ne_bot_forall_apply_mul_eq_of_mem_principalLevel_of_isKfSmooth_of_differentiable

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_ne_bot_forall_apply_mul_eq_of_mem_principalLevel_of_isKfSmooth_of_differentiable
    (K : Type) [Field K] [NumberField K]
    (ψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
    (_hψsm : ∀ s, IsKfSmooth K (ψ s))
    (_hψhol : ∀ g : AdelicGL2 (𝓞 K) K, Differentiable ℂ (fun s => ψ s g)) :
    ∃ N' : Ideal (𝓞 K), N' ≠ ⊥ ∧
      ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K, ψ s (g * u) = ψ s g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_ne_bot_forall_apply_mul_eq_of_mem_principalLevel_of_isKfSmooth_of_differentiable.solution
