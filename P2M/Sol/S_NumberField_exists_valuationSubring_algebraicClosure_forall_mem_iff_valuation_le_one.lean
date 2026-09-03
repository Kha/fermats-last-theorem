import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one
import P2M.Util
namespace P2MW.S_NumberField_exists_valuationSubring_algebraicClosure_forall_mem_iff_valuation_le_one
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField.LevelArith NumberField.PlaceTransport NumberField Pointwise

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

open NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith

theorem solution
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥F)) :
    ∃ B : ValuationSubring (AlgebraicClosure ℚ), ∀ x : ↥F, (x : AlgebraicClosure ℚ) ∈ B ↔ v.valuation ↥F x ≤ 1 :=
  NumberField.exists_valuationSubring_forall_map_mem_iff_valuation_le_one ↥F (algebraMap ↥F (AlgebraicClosure ℚ)) v
