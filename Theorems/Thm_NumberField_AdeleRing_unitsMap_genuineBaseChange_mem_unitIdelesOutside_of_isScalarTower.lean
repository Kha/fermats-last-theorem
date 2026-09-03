import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
p2m_open "CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand~adeleBaseChange_local_rigidity NumberField.LevelArith"
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

theorem NumberField.AdeleRing.unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K'']
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ x : (AdeleRing (𝓞 K) K)ˣ,
      x ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} →
      Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K K'').β.toMonoidHom x ∈
        NumberField.AdeleRing.unitIdelesOutside (𝓞 K'') K'' {w | w.under (𝓞 E) ∈ S}) ∧
    (∀ x : NumberField.SUnits.sUnitsRep E K S, ∃ x'' : NumberField.SUnits.sUnitsRep E K'' S,
      NumberField.SUnits.val E K'' S x'' = Units.map (algebraMap K K'' : K →* K'') (NumberField.SUnits.val E K S x)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower.solution
