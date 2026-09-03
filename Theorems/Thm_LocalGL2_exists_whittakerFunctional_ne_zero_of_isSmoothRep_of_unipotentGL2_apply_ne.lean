import Mathlib
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LocalGL2_exists_whittakerFunctional_ne_zero_of_isSmoothRep_of_unipotentGL2_apply_ne
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField
open FLT.SmoothAdmissibleSchurCommutant

theorem LocalGL2.exists_whittakerFunctional_ne_zero_of_isSmoothRep_of_unipotentGL2_apply_ne
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : GL (Fin 2) (v.adicCompletion K) →* Module.End ℂ V)
    (hsm : IsSmoothRep π)
    (x₀ : v.adicCompletion K) (w₀ : V) (hw₀ : π (AutomorphicForm.unipotentGL2 x₀) w₀ ≠ w₀) :
    ∃ ψ : AddChar (v.adicCompletion K) ℂ, ψ ≠ 1 ∧
      ∃ Λ : V →ₗ[ℂ] ℂ, Λ ≠ 0 ∧
        ∀ (x : v.adicCompletion K) (w : V), Λ (π (AutomorphicForm.unipotentGL2 x) w) = ψ x * Λ w := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_exists_whittakerFunctional_ne_zero_of_isSmoothRep_of_unipotentGL2_apply_ne.solution
