import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_NumberField_unitsMap_algebraMap_mem_range_idelicNorm_of_forall_exists_norm_eq
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem NumberField.unitsMap_algebraMap_mem_range_idelicNorm_of_forall_exists_norm_eq
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    [FiniteDimensional E M] [IsGalois E M]
    (a : Eˣ)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 E), ∃ z : w.adicCompletion E ⊗[E] M,
      Algebra.norm (w.adicCompletion E) z = algebraMap E (w.adicCompletion E) (a : E))
    (hinf : ∃ z : InfiniteAdeleRing E ⊗[E] M,
      Algebra.norm (InfiniteAdeleRing E) z = algebraMap E (InfiniteAdeleRing E) (a : E)) :
    Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) a ∈
      (M4aHerbrand.GenuineDescent.genuineBaseChange E M).idelicNorm.range := by p2m_exact_reverting @_root_.P2MW.S_NumberField_unitsMap_algebraMap_mem_range_idelicNorm_of_forall_exists_norm_eq.solution
