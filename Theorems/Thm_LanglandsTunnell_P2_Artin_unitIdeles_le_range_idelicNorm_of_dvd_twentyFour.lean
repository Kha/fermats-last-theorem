import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_Artin_unitIdeles_le_range_idelicNorm_of_dvd_twentyFour
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.P2.Artin.unitIdeles_le_range_idelicNorm_of_dvd_twentyFour
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (ℓ k : ℕ) (hℓ : ℓ.Prime) (hexp : ∀ x : F ≃ₐ[E] F, x ^ (ℓ ^ k) = 1) (hk : ℓ ^ k ∣ 24)
    (hdeg : Module.finrank E F ∣ 24)
    (𝔣 : Ideal (𝓞 E)) (hadm : IsAdmissibleModulus E F 𝔣) :
    unitIdeles E 𝔣 ≤ ((genuineBaseChange E F).idelicNorm).range := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_Artin_unitIdeles_le_range_idelicNorm_of_dvd_twentyFour.solution
