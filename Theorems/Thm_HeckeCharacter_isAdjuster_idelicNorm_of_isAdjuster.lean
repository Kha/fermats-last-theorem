import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem HeckeCharacter.isAdjuster_idelicNorm_of_isAdjuster (A B : Type*) [Field A]
    [NumberField A] [Field B] [NumberField B] [Algebra A B] (𝔪 : Ideal (𝓞 A))
    {v : (AdeleRing (𝓞 B) B)ˣ} {α : Bˣ} :
    HeckeCharacter.IsAdjuster B (HeckeCharacter.modulusExt A B 𝔪) v α →
      HeckeCharacter.IsAdjuster A 𝔪
        ((M4aHerbrand.GenuineDescent.genuineBaseChange A B).idelicNorm v)
        (Units.map (Algebra.norm A) α) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster.solution
