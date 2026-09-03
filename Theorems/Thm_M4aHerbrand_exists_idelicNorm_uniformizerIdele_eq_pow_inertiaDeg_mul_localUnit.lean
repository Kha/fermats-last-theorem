import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import P2M.Util
import P2M.Sol.S_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (𝔓 : HeightOneSpectrum (𝓞 M)) :
    ∃ t : ((𝔓.under (𝓞 K)).adicCompletion K)ˣ, Valued.v (t : (𝔓.under (𝓞 K)).adicCompletion K) = 1 ∧
      (M4aHerbrand.GenuineDescent.genuineBaseChange K M).idelicNorm (AutomorphicForm.uniformizerIdele M 𝔓) =
        AutomorphicForm.uniformizerIdele K (𝔓.under (𝓞 K)) ^ ((𝔓.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓.asIdeal) *
          Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
            (NumberField.AdelicLevel.localUnit (𝓞 K) K (𝔓.under (𝓞 K)) t) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit.solution
