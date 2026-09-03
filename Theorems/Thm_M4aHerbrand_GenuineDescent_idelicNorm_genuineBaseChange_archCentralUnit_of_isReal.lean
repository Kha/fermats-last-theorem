import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import P2M.Util
import P2M.Sol.S_M4aHerbrand_GenuineDescent_idelicNorm_genuineBaseChange_archCentralUnit_of_isReal
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

p2m_open "NumberField M4aHerbrand~genuineAdelicNorm_componentwise M4aHerbrand.GenuineDescent AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

theorem M4aHerbrand.GenuineDescent.idelicNorm_genuineBaseChange_archCentralUnit_of_isReal
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (x : ℝˣ) :
    (genuineBaseChange ℚ K).idelicNorm
        (AdelicVolume.archCentralUnit K w
          (Units.mapEquiv (ringEquivRealOfIsReal hw).symm.toMulEquiv x)) =
      AdelicVolume.archCentralUnit ℚ Rat.infinitePlace
        (Units.mapEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toMulEquiv x) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_GenuineDescent_idelicNorm_genuineBaseChange_archCentralUnit_of_isReal.solution
