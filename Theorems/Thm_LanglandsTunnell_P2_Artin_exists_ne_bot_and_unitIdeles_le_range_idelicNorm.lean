import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_Artin_exists_ne_bot_and_unitIdeles_le_range_idelicNorm
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative

theorem LanglandsTunnell.P2.Artin.exists_ne_bot_and_unitIdeles_le_range_idelicNorm
    (F N : Type*) [Field F] [NumberField F] [Field N] [NumberField N] [Algebra F N] [IsGalois F N]
    [IsMulCommutative (N ≃ₐ[F] N)] :
    ∃ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ ∧
      (∀ w : HeightOneSpectrum (𝓞 F), (primeAbove F N w).inertia (N ≃ₐ[F] N) ≠ ⊥ → w.asIdeal ∣ 𝔪) ∧
      unitIdeles F 𝔪 ≤ (genuineBaseChange F N).idelicNorm.range := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_Artin_exists_ne_bot_and_unitIdeles_le_range_idelicNorm.solution
