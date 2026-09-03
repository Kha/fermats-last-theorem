import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

theorem Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
    {D : Type*} [Ring D] [Algebra ℚ D] (Λ₁ Λ₂ : Submodule ℤ D)
    (h₁fg : Λ₁.FG) (h₁sp : Submodule.span ℚ (Λ₁ : Set D) = ⊤)
    (h₂fg : Λ₂.FG) (h₂sp : Submodule.span ℚ (Λ₂ : Set D) = ⊤) (hle : Λ₂ ≤ Λ₁) :
    Λ₂.toAddSubgroup.relIndex Λ₁.toAddSubgroup =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), (Submodule.localBox Λ₂ v).relIndex (Submodule.localBox Λ₁ v) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox.solution
