import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_HeckeCharacter_fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem HeckeCharacter.fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit (A B : Type*)
    [Field A] [NumberField A] [Field B] [NumberField B] [Algebra A B]
    (v : (AdeleRing (𝓞 B) B)ˣ) :
    HeckeCharacter.fadContentHom A (HeckeCharacter.projFin A
        ((M4aHerbrand.GenuineDescent.genuineBaseChange A B).idelicNorm v)) =
      HeckeCharacter.fracRelNormUnit A B
        (HeckeCharacter.fadContentHom B (HeckeCharacter.projFin B v)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit.solution
