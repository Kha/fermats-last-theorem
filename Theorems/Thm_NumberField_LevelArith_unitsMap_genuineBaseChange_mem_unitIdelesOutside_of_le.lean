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
import P2M.Sol.S_NumberField_LevelArith_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
p2m_open "CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand~adeleBaseChange_local_rigidity NumberField.LevelArith"
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

theorem NumberField.LevelArith.unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le
    (S : Finset Nat.Primes)
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F]
    (L₁ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL₁ : L ≤ L₁) (hL₁F₁ : L₁ ≤ F₁) (hFF₁ : F ≤ F₁)
    [FiniteDimensional ℚ ↥L₁] [FiniteDimensional ℚ ↥F₁]
    [Algebra ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)]
    (halg : ∀ x : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) x : ↥(levelField L₁ F₁ hL₁F₁)) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)) :
    (∀ x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ,
      x ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)} →
      Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)).β.toMonoidHom x ∈
        NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥(levelField L₁ F₁ hL₁F₁) {w | w.under (𝓞 ↥L₁) ∈ (placesOverPrimesFinset ↥L₁ S)}) ∧
    (∀ x : (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), ∃ x' : (NumberField.SUnits.sUnitsRep ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)),
      NumberField.SUnits.val ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S) x' = Units.map (algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) : ↥(levelField L F hLF) →* ↥(levelField L₁ F₁ hL₁F₁)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le.solution
